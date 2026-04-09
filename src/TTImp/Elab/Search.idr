-- Stronger proof search: case-splitting with explicit recursion for full induction.
--
-- When `searchVar` (direct unification-based search) fails, this module
-- attempts to make progress by case-splitting on unrestricted local variables
-- whose types are fully-applied data type constructors (NTCon).  For each
-- candidate variable it constructs an ICase expression.
--
-- NEW: For recursive constructors, generates explicit recursive calls instead
-- of nested %search. This enables full structural induction with induction
-- hypotheses available in recursive branches.
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

-- Generate the list [0, 1, ..., n-1]
upTo : Nat -> List Nat
upTo 0     = []
upTo (S n) = upTo n ++ [n]

-- Count the number of *explicit* Pi binders at the head of a term.
-- Works for both open and closed terms (vars is implicit and polymorphic).
countExplicit : {vars : _} -> Term vars -> Nat
countExplicit (Bind _ _ (Pi _ _ Explicit _) sc) = S (countExplicit sc)
countExplicit (Bind _ _ (Pi _ _ _ _) sc)        = countExplicit sc
countExplicit _                                  = 0

-- Retrieve the data constructors for a named type from the global context.
getDataCons : {auto c : Ref Ctxt Defs} -> Name -> Core (List Name)
getDataCons n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure []
         let TCon _ _ _ _ _ (Just cons) _ = definition gdef
              | _ => pure []
         pure cons

-- Build the pattern `Con arg0 arg1 ...` with fresh IBindVars for every
-- explicit argument.  conIdx is used to make bind-var names unique across
-- the alternatives of the same ICase expression.
buildConPat : FC -> Name -> (arity : Nat) -> (conIdx : Nat) -> RawImp
buildConPat fc con arity conIdx =
    let args = map (\j => IBindVar fc (UN (Basic ("__cs" ++ show conIdx ++ "_" ++ show j))))
                   (upTo arity)
    in foldl (IApp fc) (IVar fc con) args

-- A local variable that is a valid candidate for case-splitting:
-- unrestricted multiplicity + the head of its type is a TCon.
record SplitCandidate where
  constructor MkSplit
  varName   : Name   -- local variable to split on
  tyConName : Name   -- head type constructor of its normalised type

-- Walk the environment, collecting split candidates.
-- Only unrestricted (top-multiplicity) bindings whose normalised type
-- is a fully-applied NTCon with at least one data constructor are included.
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

-- Local zipWith3 (not in Prelude)
zipWith3 : (a -> b -> c -> d) -> List a -> List b -> List c -> List d
zipWith3 _ []        _        _        = []
zipWith3 _ _         []       _        = []
zipWith3 _ _         _        []       = []
zipWith3 f (x :: xs) (y :: ys) (z :: zs)
    = f x y z :: zipWith3 f xs ys zs

-- Check if a term is an equality type (=) by looking at the name
isEquality : Term vars -> Bool
isEquality (App _ (App _ (Ref _ _ n) _) _) =
    case n of
        UN (Basic "=") => True
        _ => False
isEquality _ = False

-- Build a recursive call: `f arg` where f is the function being defined
buildRecCall : FC -> Name -> RawImp -> RawImp
buildRecCall fc fName arg = IApp fc (IVar fc fName) arg

-- Build `cong f eq` for lifting an equality through a constructor
buildCong : FC -> Name -> RawImp -> RawImp
buildCong fc fName eq =
    IApp fc (IApp fc (IVar fc (UN $ Basic "cong")) (IVar fc fName)) eq

-- Try case-split proof search as a fallback when searchVar fails.
--
-- For each local variable `x : D args` (unrestricted, D a data type), builds:
--
--   case x of
--     C0 a0_0 ... => %search(depth-1)
--     C1 a1_0 ... => %search(depth-1)  or  cong S (f a1_0) for recursive
--     ...
--
-- and elaborates it against the expected type topTy.  Returns the first
-- candidate that succeeds.  Caller must ensure depth >= 2.
export
tryCaseSplitSearch : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto m : Ref MD Metadata} ->
                     {auto u : Ref UST UState} ->
                     {auto e : Ref EST (EState vars)} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     FC -> RigCount -> (depth : Nat) ->
                     ElabInfo ->
                     NestedNames vars -> Env Term vars ->
                     (topTy : Term vars) ->
                     Core (Term vars)
tryCaseSplitSearch fc rig depth elabinfo nest env topTy
    = do est <- get EST
         let fName = Resolved (defining est)  -- function being defined
         candidates <- getSplitCandidates env
         log "auto" 3 $ "case-split search: "
                       ++ show (length candidates) ++ " candidate(s)"
         tryAll fName candidates
  where
    -- One ICase alternative with explicit recursion support
    -- conIdx: index of this constructor (0 for first, etc.)
    makeAlt : Name -> Name -> Name -> Nat -> Nat -> ImpClause
    makeAlt fName tyCon con arity conIdx =
        let pat = buildConPat fc con arity conIdx
            -- Generate argument names for the pattern
            argNames = map (\j => UN $ Basic ("__cs" ++ show conIdx ++ "_" ++ show j)) (upTo arity)
            -- For recursive constructors with equality goals, try explicit recursion
            body = if isEquality topTy
                then
                    -- Simple heuristic: nullary constructors are base cases
                    -- constructors with arguments are recursive
                    case arity of
                        Z => ISearch fc (depth `minus` 1)  -- base case: Z, True, False, Nil
                        S _ =>
                            -- recursive case: S, ::, etc.
                            -- Generate: cong Con (f recArg)
                            case argNames of
                                [] => ISearch fc (depth `minus` 1)
                                (recArg :: _) =>
                                    -- Apply cong to lift the recursive call
                                    buildCong fc con (buildRecCall fc fName (IVar fc recArg))
                else ISearch fc (depth `minus` 1)  -- not equality, use search
        in PatClause fc pat body

    -- Attempt to solve via a single candidate; save+restore state on failure
    trySplit : Name -> SplitCandidate -> Core (Term vars)
    trySplit fName (MkSplit varNm tyConNm)
        = do log "auto" 5 $ "  trying split on " ++ show varNm
             cons    <- getDataCons tyConNm
             arities <- traverse (\con => do
                            defs <- get Ctxt
                            Just gdef <- lookupCtxtExact con (gamma defs)
                                 | Nothing => pure 0
                            pure (countExplicit (type gdef))) cons
             let alts    = zipWith3 (makeAlt fName tyConNm) cons arities (upTo (length cons))
             let caseExpr = ICase fc [] (IVar fc varNm)
                                   (Implicit fc False) alts
             ust  <- get UST
             defs <- branch
             catch
               (do (tm, _) <- check rig elabinfo nest env caseExpr
                                     (Just (gnf env topTy))
                   commit
                   pure tm)
               (\err => do put UST ust
                           put Ctxt defs
                           throw err)

    -- Try each candidate left to right; return the first that succeeds
    tryAll : Name -> List SplitCandidate -> Core (Term vars)
    tryAll _ []
        = throw (InternalError "tryCaseSplitSearch: no split succeeded")
    tryAll fName (c :: cs)
        = catch (trySplit fName c) (\_ => tryAll fName cs)
