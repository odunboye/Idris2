module Core.UnivSolver

-- Universe level constraint solver (Phase 3).
--
-- Constraints have the form `l ≤ r` where l and r are UnivLevel expressions.
-- The solver assigns a concrete Nat to each UVar so that every constraint
-- is satisfied.  If no satisfying assignment exists (e.g. USucc u ≤ u) a
-- cycle error is reported.
--
-- Algorithm: greedy greatest-lower-bound propagation (worklist fixpoint).
--   1. Initialise every UVar to level 0.
--   2. For each constraint (l, r): if eval(l) > eval(r), bump UVar(s) in r.
--   3. Repeat until stable (no changes) or iteration limit exceeded.
--   4. Iteration limit exceeded → cyclic constraints (universe inconsistency).

import Core.FC
import Core.Name
import Core.Name.Scoped
import Core.TT.Binder
import Core.TT.Term

import Data.List
import Data.Maybe
import Data.SortedMap

%default total

-- A solved universe level assignment: Name -> Nat
public export
UnivAssignment : Type
UnivAssignment = SortedMap Name Nat

-- Evaluate a UnivLevel under an assignment.  Unknown UVars default to 0.
export
evalLevel : UnivAssignment -> UnivLevel -> Nat
evalLevel assign UZero        = 0
evalLevel assign (UVar n)     = fromMaybe 0 (lookup n assign)
evalLevel assign (USucc u)    = S (evalLevel assign u)
evalLevel assign (UMax l r)   = max (evalLevel assign l) (evalLevel assign r)

-- Collect all UVar names occurring in a UnivLevel.
collectVars : UnivLevel -> List Name
collectVars UZero        = []
collectVars (UVar n)     = [n]
collectVars (USucc u)    = collectVars u
collectVars (UMax l r)   = collectVars l ++ collectVars r

-- Bump every UVar in a level so that `eval assign level >= target`.
-- For `UMax`, we bump both branches (safe over-approximation).
bumpLevel : UnivAssignment -> UnivLevel -> Nat -> UnivAssignment
bumpLevel assign UZero        _      = assign   -- can't bump a constant
bumpLevel assign (UVar n)     target =
  let current = fromMaybe 0 (lookup n assign) in
  if target > current
    then insert n target assign
    else assign
bumpLevel assign (USucc u)    target =
  -- USucc u >= target iff u >= target - 1
  case target of
    Z   => assign               -- already satisfied
    S k => bumpLevel assign u k
bumpLevel assign (UMax l r)   target =
  -- bump both branches; either path can satisfy the constraint
  let assign' = bumpLevel assign l target in
  bumpLevel assign' r target

-- One pass over all constraints.  Returns (assignment, changed).
onePass : UnivAssignment
        -> List (UnivLevel, UnivLevel)
        -> (UnivAssignment, Bool)
onePass assign [] = (assign, False)
onePass assign ((l, r) :: rest) =
  let lv    = evalLevel assign l
      rv    = evalLevel assign r
      (a', changed') =
        if lv > rv
          then (bumpLevel assign r lv, True)
          else (assign, False)
      (a'', changed'') = onePass a' rest
  in (a'', changed' || changed'')

-- Run the fixpoint.  `fuel` limits iterations to detect divergence.
solve : Nat -> UnivAssignment -> List (UnivLevel, UnivLevel)
      -> Maybe UnivAssignment
solve Z _ _ = Nothing   -- fuel exhausted → cycle
solve (S fuel) assign cs =
  let (assign', changed) = onePass assign cs in
  if changed
    then solve fuel assign' cs
    else Just assign'

-- Maximum iterations before declaring a cycle.
-- Each iteration can increase at most one variable by at least 1, so a
-- satisfying assignment with max-level k needs at most (n*k) iterations
-- where n = |vars|.  We use a generous bound.
iterationLimit : Nat
iterationLimit = 10000

-- Build the initial assignment: all known UVars start at 0.
initAssign : List (UnivLevel, UnivLevel) -> UnivAssignment
initAssign cs =
  let vars = cs >>= \(l, r) => collectVars l ++ collectVars r
  in foldl (\a, n => if isJust (lookup n a) then a else insert n 0 a) empty vars

-- Main entry point.
-- Returns Left error-message or Right assignment.
export
solveUniverse : List (UnivLevel, UnivLevel) -> Either String UnivAssignment
solveUniverse [] = Right empty
solveUniverse cs =
  let assign0 = initAssign cs in
  case solve iterationLimit assign0 cs of
    Nothing => Left "Universe inconsistency: cyclic universe level constraints"
    Just a  =>
      -- Final check: verify all constraints are satisfied.
      let unsatisfied = filter (\(l, r) => evalLevel a l > evalLevel a r) cs in
      case unsatisfied of
        []      => Right a
        _       => Left "Universe inconsistency: unsatisfiable level constraints"

-- Structural less-than-or-equal comparison on UnivLevel.
-- Returns Just True  if provably ul ≤ ur from structure alone.
-- Returns Just False if provably ul > ur.
-- Returns Nothing   if the comparison depends on UVar assignments.
-- Used by the conversion checker (Phase 5) for cumulativity without
-- needing access to UST.
export
leqUnivLevel : UnivLevel -> UnivLevel -> Maybe Bool
leqUnivLevel UZero     _          = Just True    -- 0 ≤ anything
leqUnivLevel _         UZero      = Nothing      -- n ≤ 0 only if n = 0 (need to know n)
leqUnivLevel (UVar n)  (UVar m)   =
  if n == m then Just True else Nothing           -- same var: equal; different: unknown
leqUnivLevel (UVar _)  _          = Nothing      -- unknown variable
leqUnivLevel _          (UVar _)  = Nothing      -- unknown variable
leqUnivLevel (USucc l) (USucc r)  = leqUnivLevel l r
leqUnivLevel (USucc _) UZero      = Just False   -- n+1 > 0
leqUnivLevel UZero     (USucc _)  = Just True    -- 0 < n+1
leqUnivLevel (UMax a b) r         =              -- max(a,b) ≤ r iff a ≤ r AND b ≤ r
  case (leqUnivLevel a r, leqUnivLevel b r) of
    (Just True,  Just True)  => Just True
    (Just False, _)          => Just False
    (_,          Just False) => Just False
    _                        => Nothing
leqUnivLevel l         (UMax a b) =              -- l ≤ max(a,b) iff l ≤ a OR l ≤ b
  case (leqUnivLevel l a, leqUnivLevel l b) of
    (Just True,  _)          => Just True
    (_,          Just True)  => Just True
    (Just False, Just False) => Just False
    _                        => Nothing

-- Helpers for natToLevel, used by applyAssign and applyAssignToTerm.
natToLevel : Nat -> UnivLevel
natToLevel Z     = UZero
natToLevel (S k) = USucc (natToLevel k)

-- Substitute solved levels into a UnivLevel expression.
export
applyAssign : UnivAssignment -> UnivLevel -> UnivLevel
applyAssign assign UZero        = UZero
applyAssign assign (UVar n)     =
  case lookup n assign of
    Nothing => UVar n      -- unresolved; keep as-is
    Just k  => natToLevel k
applyAssign assign (USucc u)    = USucc (applyAssign assign u)
applyAssign assign (UMax l r)   = UMax (applyAssign assign l) (applyAssign assign r)

-- Apply a solved UnivAssignment to every TType node in a Term.
-- This is the back-substitution step: after solving, concretise all
-- universe metavariables in the elaborated term.
mutual
  export
  covering
  applyAssignToTerm : UnivAssignment -> Term vars -> Term vars
  applyAssignToTerm assign (Local fc isLet idx p)   = Local fc isLet idx p
  applyAssignToTerm assign (Ref fc nt n)            = Ref fc nt n
  applyAssignToTerm assign (Meta fc n i args)
      = Meta fc n i (map (applyAssignToTerm assign) args)
  applyAssignToTerm assign (Bind fc x b scope)
      = Bind fc x (applyAssignToBinder assign b)
                  (applyAssignToTerm assign scope)
  applyAssignToTerm assign (App fc fn arg)
      = App fc (applyAssignToTerm assign fn) (applyAssignToTerm assign arg)
  applyAssignToTerm assign (As fc s as pat)
      = As fc s (applyAssignToTerm assign as) (applyAssignToTerm assign pat)
  applyAssignToTerm assign (TDelayed fc r ty)
      = TDelayed fc r (applyAssignToTerm assign ty)
  applyAssignToTerm assign (TDelay fc r ty val)
      = TDelay fc r (applyAssignToTerm assign ty) (applyAssignToTerm assign val)
  applyAssignToTerm assign (TForce fc r tm)
      = TForce fc r (applyAssignToTerm assign tm)
  applyAssignToTerm assign (PrimVal fc c) = PrimVal fc c
  applyAssignToTerm assign (Erased fc why)
      = Erased fc (map (applyAssignToTerm assign) why)
  applyAssignToTerm assign (TType fc u)
      = TType fc (applyAssign assign u)

  covering
  applyAssignToBinder : UnivAssignment -> Binder (Term vars) -> Binder (Term vars)
  applyAssignToBinder assign (Lam fc c p ty)
      = Lam fc c (map (applyAssignToTerm assign) p) (applyAssignToTerm assign ty)
  applyAssignToBinder assign (Let fc c val ty)
      = Let fc c (applyAssignToTerm assign val) (applyAssignToTerm assign ty)
  applyAssignToBinder assign (Pi fc c p ty)
      = Pi fc c (map (applyAssignToTerm assign) p) (applyAssignToTerm assign ty)
  applyAssignToBinder assign (PVar fc c p ty)
      = PVar fc c (map (applyAssignToTerm assign) p) (applyAssignToTerm assign ty)
  applyAssignToBinder assign (PLet fc c val ty)
      = PLet fc c (applyAssignToTerm assign val) (applyAssignToTerm assign ty)
  applyAssignToBinder assign (PVTy fc c ty)
      = PVTy fc c (applyAssignToTerm assign ty)
