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

-- Substitute solved levels into a UnivLevel expression.
export
applyAssign : UnivAssignment -> UnivLevel -> UnivLevel
applyAssign assign UZero        = UZero
applyAssign assign (UVar n)     =
  case lookup n assign of
    Nothing => UVar n      -- unresolved; keep as-is
    Just k  => natToLevel k
  where
    natToLevel : Nat -> UnivLevel
    natToLevel Z     = UZero
    natToLevel (S k) = USucc (natToLevel k)
applyAssign assign (USucc u)    = USucc (applyAssign assign u)
applyAssign assign (UMax l r)   = UMax (applyAssign assign l) (applyAssign assign r)
