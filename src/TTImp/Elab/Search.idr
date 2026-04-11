-- Case-splitting proof search fallback.
--
-- When `searchVar` (delayed-elaboration-based search) fails to find a proof,
-- this module tries to make progress by case-splitting on unrestricted local
-- variables whose normalised types are data type constructors (NTCon).
--
-- For each split candidate it builds an ICase expression.  Branches use:
--   * `Refl`  — for arity-0 constructors, non-recursive constructors, or
--               non-equality goals.  Succeeds when the branch goal reduces
--               definitionally to `x = x`.
--   * `cong (Con a0 … a_{n-2}) (defNm a_{n-1})` — for constructors whose
--               last explicit argument is structurally recursive w.r.t. the
--               type being split (e.g. `S : Nat -> Nat`, `(::) on List`).
--               Only generated when the goal is a propositional equality.
--
-- An `isEqualGoal` guard at `tryCaseSplitSearch` prevents the search from
-- running on type-class goals (e.g. `Eq (a, b)`), which would otherwise
-- generate ill-typed `Refl` terms and leak constraint errors as hard errors.
module TTImp.Elab.Search

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.Unify
import Core.UnifyState
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.TTImp

%default covering

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- Generate [0, 1, ..., n-1]
upTo : Nat -> List Nat
upTo 0     = []
upTo (S n) = upTo n ++ [n]

-- Count explicit Pi binders at the head of a type term.
countExplicit : {vars : _} -> Term vars -> Nat
countExplicit (Bind _ _ (Pi _ _ Explicit _) sc) = S (countExplicit sc)
countExplicit (Bind _ _ (Pi _ _ _ _) sc)        = countExplicit sc
countExplicit _                                  = 0

-- Retrieve data constructors for a fully-applied type constructor name.
getDataCons : {auto c : Ref Ctxt Defs} -> Name -> Core (List Name)
getDataCons n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure []
         let TCon _ _ _ _ _ (Just cons) _ = definition gdef
              | _ => pure []
         pure cons

-- Build the pattern `Con bv0 bv1 ...` with fresh bind-vars for every
-- explicit argument.  conIdx and argIdx together give unique names.
buildConPat : FC -> Name -> (arity : Nat) -> (conIdx : Nat) -> RawImp
buildConPat fc con arity conIdx =
    let args = map (\j => IBindVar fc (UN (Basic ("__cs" ++ show conIdx ++ "_" ++ show j))))
                   (upTo arity)
    in foldl (IApp fc) (IVar fc con) args

-- Strip application nodes to find the outermost name reference in a term.
termHead : {vars : _} -> Term vars -> Maybe Name
termHead (App _ f _) = termHead f
termHead (Ref _ _ n) = Just n
termHead _           = Nothing

-- Walk the Pi binders of a function type and return the head name of the
-- LAST explicit argument type, skipping all non-explicit binders.
-- Returns Nothing when the type has no explicit argument.
lastExplicitArgHead : {vars : _} -> Term vars -> Maybe Name
lastExplicitArgHead (Bind _ _ (Pi _ _ Explicit argTy) sc)
    = case lastExplicitArgHead sc of
        Nothing => termHead argTy   -- argTy is the last explicit arg
        Just h  => Just h           -- a later explicit arg exists
lastExplicitArgHead (Bind _ _ (Pi _ _ _ _) sc)
    = lastExplicitArgHead sc        -- skip implicit / auto-implicit binders
lastExplicitArgHead _ = Nothing

-- True iff the last explicit argument of constructor type `conTy` is
-- structurally recursive w.r.t. `targetTCon` (i.e. its type head is that
-- same type constructor).
--
-- Examples (with targetTCon = Nat / Maybe / List):
--   S    : Nat -> Nat          → True  (last arg head = Nat = target)
--   Just : a -> Maybe a        → False (last arg head = Bound, a type var)
--   (::) : a -> List a -> ...  → True  (last arg head = List = target)
--   Z    : Nat                 → False (no explicit args → Nothing)
isLastArgRecursive : {auto c : Ref Ctxt Defs} -> Term [] -> Name -> Core Bool
isLastArgRecursive conTy targetTCon
    = case lastExplicitArgHead conTy of
        Nothing => pure False
        Just nm  => catch
            (do fn1 <- getFullName nm
                fn2 <- getFullName targetTCon
                pure (fn1 == fn2))
            (\_ => pure False)

-- Check if the goal type is propositional equality after normalisation.
isEqualGoal : {vars : _} -> {auto c : Ref Ctxt Defs} ->
              Env Term vars -> Term vars -> Core Bool
isEqualGoal env ty
    = do defs <- get Ctxt
         nty  <- nf defs env ty
         case nty of
           NTCon _ n _ _ => isEqualTy n
           _              => pure False

-- A variable worth splitting on: unrestricted multiplicity and the head of
-- its normalised type is a type constructor with at least one constructor.
record SplitCandidate where
  constructor MkSplit
  varName   : Name
  tyConName : Name

-- Walk the elaboration environment collecting split candidates.
getSplitCandidates : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     Env Term vars ->
                     Core (List SplitCandidate)
getSplitCandidates [] = pure []
getSplitCandidates {vars = v :: vs} (b :: env)
    = do rest <- getSplitCandidates env
         if multiplicity b /= top
           then pure rest
           else do defs <- get Ctxt
                   nty  <- nf defs env (binderType b)
                   case nty of
                     NTCon _ n _ _ =>
                       do cons <- getDataCons n
                          if isNil cons
                            then pure rest
                            else pure (MkSplit v n :: rest)
                     _ => pure rest

------------------------------------------------------------------------
-- Core: tryCaseSplitSearch
------------------------------------------------------------------------

-- Build the body of one case alternative.
--
-- * mDefNm = Nothing    → `Refl`  (non-equality goal, or non-recursive con)
-- * mDefNm = Just defNm AND arity = 0 → `Refl`  (base case)
-- * mDefNm = Just defNm AND arity > 0 →
--     `cong (Con a0 … a_{n-2}) (defNm a_{n-1})`
--   where a_{n-1} is the recursive (last explicit) argument.
makeAltBody : FC -> Name -> (arity : Nat) -> (conIdx : Nat) -> Maybe Name -> RawImp
makeAltBody fc _   _     _      Nothing     = IVar fc (UN (Basic "Refl"))
makeAltBody fc _   0     _      (Just _)    = IVar fc (UN (Basic "Refl"))
makeAltBody fc con arity conIdx (Just defNm) =
    let recArgIdx  = arity `minus` 1
        recArgNm   = UN (Basic ("__cs" ++ show conIdx ++ "_" ++ show recArgIdx))
        -- Prefix args: partially apply constructor to all but the last arg.
        prefixArgs = map (\j => IVar fc (UN (Basic ("__cs" ++ show conIdx ++ "_" ++ show j))))
                         (upTo recArgIdx)
        conFun     = foldl (IApp fc) (IVar fc con) prefixArgs
        recCall    = IApp fc (IVar fc defNm) (IVar fc recArgNm)
    in IApp fc (IApp fc (IVar fc (UN (Basic "cong"))) conFun) recCall

-- Build one case alternative.
makeAlt : FC -> Name -> (arity : Nat) -> (conIdx : Nat) -> Maybe Name -> ImpClause
makeAlt fc con arity conIdx mDefNm =
    PatClause fc (buildConPat fc con arity conIdx) (makeAltBody fc con arity conIdx mDefNm)

-- Try to solve `topTy` by case-splitting on a single candidate variable.
--
-- ALL Core operations are inside the `catch` block so that any failure
-- (including intermediate context queries) restores state cleanly and does
-- not leak constraint errors as hard diagnostics.
trySplit : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           FC -> RigCount -> Nat ->
           ElabInfo -> NestedNames vars -> Env Term vars ->
           Term vars ->
           SplitCandidate ->
           Core (Term vars)
trySplit fc rig depth elabinfo nest env topTy (MkSplit varNm tyConNm)
    = do log "auto" 5 $ "  trying split on " ++ show varNm
         ust     <- get UST
         ctxSnap <- branch
         catch
           (do cons   <- getDataCons tyConNm
               defs   <- get Ctxt
               eqGoal <- isEqualGoal env topTy
               est    <- get EST
               let defNm : Name = Resolved (defining est)
               alts <- traverse (\(conIdx, con) =>
                          do Just gdef <- lookupCtxtExact con (gamma defs)
                                 | Nothing => pure (makeAlt fc con 0 conIdx Nothing)
                             let arity = countExplicit (type gdef)
                             isRec <- isLastArgRecursive (type gdef) tyConNm
                             let mDefNm : Maybe Name =
                                     if eqGoal && isRec then Just defNm else Nothing
                             pure (makeAlt fc con arity conIdx mDefNm))
                         (zip (upTo (length cons)) cons)
               let caseExpr = ICase fc [] (IVar fc varNm) (Implicit fc False) alts
               log "auto" 5 $ "  built case with " ++ show (length alts) ++ " alternatives"
               (tm, _) <- check rig elabinfo nest env caseExpr (Just (gnf env topTy))
               commit
               log "auto" 5 "  case split succeeded"
               pure tm)
           (\err =>
             do put UST ust
                put Ctxt ctxSnap
                throw err)

-- Try case-splitting on each candidate in turn; return the first success.
--
-- Only runs for propositional equality goals.  Skips type-class goals
-- (e.g. `Eq (a, b)`) immediately so they fall back to `searchVar` cleanly
-- without generating ill-typed terms that leak as hard constraint errors.
export
tryCaseSplitSearch : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto m : Ref MD Metadata} ->
                     {auto u : Ref UST UState} ->
                     {auto e : Ref EST (EState vars)} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     FC -> RigCount -> Nat ->
                     ElabInfo -> NestedNames vars -> Env Term vars ->
                     Term vars ->
                     Core (Term vars)
tryCaseSplitSearch fc rig depth elabinfo nest env topTy
    = do isEq <- isEqualGoal env topTy
         if not isEq
           then throw (InternalError "tryCaseSplitSearch: not an equality goal")
           else do
             candidates <- getSplitCandidates env
             log "auto" 3 $ "case-split search: " ++ show (length candidates) ++ " candidate(s)"
             tryAll candidates
  where
    tryAll : List SplitCandidate -> Core (Term vars)
    tryAll []
        = throw (InternalError "tryCaseSplitSearch: no split succeeded")
    tryAll (c :: cs)
        = catch (trySplit fc rig depth elabinfo nest env topTy c)
                (\_ => tryAll cs)
