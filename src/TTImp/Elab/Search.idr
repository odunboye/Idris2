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
--
-- NEW: Supports computational goals like `plus n 0 = n` by allowing
-- definitional equality after case splitting.
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
         -- Normalize the goal type to unfold definitions like `plus n 0`
         defs <- get Ctxt
         normTopTy <- nf defs env topTy
         logTermNF "auto" 5 "Case-split goal" env topTy
         candidates <- getSplitCandidates env
         log "auto" 3 $ "case-split search: "
                       ++ show (length candidates) ++ " candidate(s)"
         tryAll fName normTopTy candidates
  where
    -- Build the body for a case alternative
    -- For equality goals with recursive constructors, generates explicit recursion
    buildAltBody : Name -> Name -> Name -> Nat -> Nat -> List Name -> NF vars -> Core RawImp
    buildAltBody fName tyCon con arity conIdx argNames goalNF = do
        defs <- get Ctxt
        goalTm <- quote defs env goalNF
        let isEq = isEquality goalTm
        log "auto" 6 $ "Building body for " ++ show con ++ " (equality: " ++ show isEq ++ ")"
        
        if not isEq
            then pure $ ISearch fc (depth `minus` 1)  -- not equality, use search
            else case arity of
                Z => pure $ ISearch fc (depth `minus` 1)  -- base case
                S _ => case argNames of
                    [] => pure $ ISearch fc (depth `minus` 1)
                    (recArg :: _) => do
                        -- Generate explicit recursive call with cong
                        log "auto" 6 $ "  Generating cong " ++ show con ++ " (" ++ show fName ++ " " ++ show recArg ++ ")"
                        pure $ buildCong fc con (buildRecCall fc fName (IVar fc recArg))

    -- One ICase alternative with explicit recursion support
    makeAlt : Name -> Name -> Name -> Nat -> Nat -> NF vars -> Core ImpClause
    makeAlt fName tyCon con arity conIdx goalNF = do
        let pat = buildConPat fc con arity conIdx
        -- Generate argument names for the pattern
        let argNames = map (\j => UN $ Basic ("__cs" ++ show conIdx ++ "_" ++ show j)) (upTo arity)
        body <- buildAltBody fName tyCon con arity conIdx argNames goalNF
        pure $ PatClause fc pat body

    -- Attempt to solve via a single candidate; save+restore state on failure
    trySplit : Name -> NF vars -> SplitCandidate -> Core (Term vars)
    trySplit fName normGoal (MkSplit varNm tyConNm)
        = do log "auto" 5 $ "  trying split on " ++ show varNm
             cons    <- getDataCons tyConNm
             arities <- traverse (\con => do
                            defs <- get Ctxt
                            Just gdef <- lookupCtxtExact con (gamma defs)
                                 | Nothing => pure 0
                            pure (countExplicit (type gdef))) cons
             -- Build alternatives with the normalized goal type
             let conIndices = upTo (length cons)
             alts <- traverse (\(con, arity, conIdx) => 
                        makeAlt fName tyConNm con arity conIdx normGoal)
                     (zipWith3 (\c, a, i => (c, a, i)) cons arities conIndices)
             let caseExpr = ICase fc [] (IVar fc varNm)
                                   (Implicit fc False) alts
             log "auto" 5 $ "  Built case expression with " ++ show (length alts) ++ " alternatives"
             ust  <- get UST
             defs <- branch
             catch
               (do -- Use the NORMALIZED goal type for checking
                   -- This allows computational goals like `plus n 0 = n` to work
                   normGoalTy <- quote defs env normGoal
                   (tm, _) <- check rig elabinfo nest env caseExpr
                                     (Just (gnf env normGoalTy))
                   commit
                   log "auto" 5 $ "  Case split succeeded!"
                   pure tm)
               (\err => do 
                   log "auto" 6 $ "  Case split failed: " ++ show err
                   put UST ust
                   put Ctxt defs
                   throw err)

    -- Try each candidate left to right; return the first that succeeds
    tryAll : Name -> NF vars -> List SplitCandidate -> Core (Term vars)
    tryAll _ _ []
        = throw (InternalError "tryCaseSplitSearch: no split succeeded")
    tryAll fName normGoal (c :: cs)
        = catch (trySplit fName normGoal c) 
                (\_ => tryAll fName normGoal cs)
