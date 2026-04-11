-- Case-splitting proof search fallback.
--
-- When `searchVar` (delayed-elaboration-based search) fails to find a proof,
-- this module tries to make progress by case-splitting on unrestricted local
-- variables whose normalised types are data type constructors (NTCon).
--
-- For each split candidate it builds an ICase with Refl (for base constructors)
-- or `cong Con (f arg)` (for recursive constructors) in every branch.
-- The conversion checker then handles any definitional reductions needed to
-- make `Refl` type-check in each branch.
--
-- The `cong` branch handles inductive proofs: if the last explicit argument of a
-- constructor has the same type as the data type being split, we generate
-- `cong Con (defNm lastArg)` where `defNm` is the function being defined.
-- This makes `plusZeroRight : (n : Nat) -> plus n 0 = n` provable by %search.
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

-- IVar reference for the j-th explicit argument of constructor at index conIdx.
-- Naming matches buildConPat: __cs{conIdx}_{j}.
-- Defined as a top-level function so it can be used as a partial application
-- in map without needing a lambda (the bootstrap parser struggles with lambdas
-- inside multi-binding let blocks).
csVar : FC -> (conIdx : Nat) -> (j : Nat) -> RawImp
csVar fc conIdx j = IVar fc (UN (Basic ("__cs" ++ show conIdx ++ "_" ++ show j)))

-- Strip App nodes to find the outermost name reference in a term.
termHead : {vars : _} -> Term vars -> Maybe Name
termHead (App _ f _) = termHead f
termHead (Ref _ _ n) = Just n
termHead _ = Nothing

-- Syntactic check: does `ty` have propositional equality `(=)` as its head?
-- Does NOT call `nf`, so it is safe on goals containing unsolved metavariables.
-- Returns False for interface goals (e.g. `Eq a`) which have a different head.
export
hasPropEqHead : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Term vars -> Core Bool
hasPropEqHead ty
    = case termHead ty of
        Nothing => pure False
        Just hn => catch
          (do defs <- get Ctxt
              case rewritenames (options defs) of
                Nothing => pure False
                Just r  => do fhn <- getFullName hn
                              feq <- getFullName (equalType r)
                              pure (fhn == feq))
          (\_ => pure False)

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

-- Get the outermost Name at the head of the last explicit argument type
-- of a data constructor.  Returns Nothing for nullary constructors.
-- Used to detect recursive constructors (e.g. S : Nat -> Nat).
-- `go` is polymorphic over the variable scope because Bind nodes extend it.
lastExplicitArgHead : {auto c : Ref Ctxt Defs} ->
                      Name -> Core (Maybe Name)
lastExplicitArgHead con = do
    defs <- get Ctxt
    Just gdef <- lookupCtxtExact con (gamma defs) | Nothing => pure Nothing
    pure (go (type gdef))
  where
    go : {vs : _} -> Term vs -> Maybe Name
    go (Bind _ _ (Pi _ _ Explicit ty) sc) =
        case go sc of
          Nothing => termHead ty   -- this is the last explicit arg
          Just n  => Just n
    go (Bind _ _ _ sc) = go sc
    go _ = Nothing

-- True if the last explicit argument type of `con` has `dataTyCon` as its
-- type-constructor head — i.e. `con` is a recursive constructor.
-- Example: isLastArgRecursive S Nat = True; isLastArgRecursive Z Nat = False.
isLastArgRecursive : {auto c : Ref Ctxt Defs} ->
                     (con : Name) -> (dataTyCon : Name) -> Core Bool
isLastArgRecursive con dataTyCon = do
    mh <- lastExplicitArgHead con
    case mh of
      Nothing => pure False
      Just h  => do fh  <- getFullName h
                    fdt <- getFullName dataTyCon
                    pure (fh == fdt)

------------------------------------------------------------------------
-- Core: tryCaseSplitSearch
------------------------------------------------------------------------

-- Build the body of one ICase alternative.
-- For non-recursive constructors: Refl.
-- For recursive constructors: cong (Con prefixArgs) (defNm lastArg).
--
-- Variable names must match buildConPat's naming scheme: __cs{conIdx}_{j}.
makeAltBody : FC -> Name -> Nat -> Nat -> Bool -> Name -> RawImp
makeAltBody fc con arity conIdx isRec defNm =
    if isRec
    then IApp fc
             (IApp fc (IVar fc (UN (Basic "cong")))
                      (foldl (IApp fc) (IVar fc con)
                             (map (csVar fc conIdx) (upTo (minus arity 1)))))
             (IApp fc (IVar fc defNm) (csVar fc conIdx (minus arity 1)))
    else IVar fc (UN (Basic "Refl"))

-- Build one ICase alternative: pattern matching on constructor `con` with
-- `arity` explicit arguments.
-- If isRec, body is `cong (Con prefixArgs) (defNm lastArg)`;
-- otherwise body is `Refl`.
makeAlt : FC -> Name -> (arity : Nat) -> (conIdx : Nat) ->
          (isRec : Bool) -> (defNm : Name) -> ImpClause
makeAlt fc con arity conIdx isRec defNm =
    let pat  = buildConPat fc con arity conIdx
        body = makeAltBody fc con arity conIdx isRec defNm
    in PatClause fc pat body

-- Try to solve `topTy` by case-splitting on a single candidate variable.
-- Saves and restores the unification and context state on failure.
-- All operations (including isLastArgRecursive) run inside the catch block
-- so that context side-effects are rolled back cleanly on failure.
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
         -- Snapshot before any context-affecting operations.
         ust     <- get UST
         ctxSnap <- branch
         catch
           (do -- Get the name of the function being defined for recursive calls.
               est <- get EST
               let defNm = Resolved (defining est)
               -- Build case alternatives with Refl or cong bodies.
               cons <- getDataCons tyConNm
               defs <- get Ctxt
               alts <- traverse
                         (\p => do
                             let (conIdx, con) = p
                             Just gdef <- lookupCtxtExact con (gamma defs)
                                 | Nothing => pure (makeAlt fc con 0 conIdx False defNm)
                             let arity = countExplicit (type gdef)
                             isRec <- isLastArgRecursive con tyConNm
                             pure (makeAlt fc con arity conIdx isRec defNm))
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
-- Throws InternalError if all candidates fail (caller catches and falls back).
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
    = do candidates <- getSplitCandidates env
         log "auto" 3 $ "case-split search: " ++ show (length candidates) ++ " candidate(s)"
         tryAll candidates
  where
    tryAll : List SplitCandidate -> Core (Term vars)
    tryAll []
        = throw (InternalError "tryCaseSplitSearch: no split succeeded")
    tryAll (c :: cs)
        = catch (trySplit fc rig depth elabinfo nest env topTy c)
                (\_ => tryAll cs)
