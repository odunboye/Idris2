-- Sub-problem A: auto-sym rewrite.
-- When prf : lt = rt and the goal contains rt (not lt),
-- `rewrite prf` should automatically use `sym prf` to rewrite rt → lt.
module AutoSym

import Data.Vect

plusZeroRight : (n : Nat) -> n + 0 = n
plusZeroRight 0 = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

-- Classic case: prf : n+0 = n, goal has 'n' not 'n+0'.
-- Without auto-sym the user must write `rewrite sym prf in xs`.
coerce_auto : (0 prf : n + 0 = n) -> Vect (n + 0) a -> Vect n a
coerce_auto prf xs = rewrite prf in xs

-- Explicit sym still works too.
coerce_sym : (0 prf : n + 0 = n) -> Vect (n + 0) a -> Vect n a
coerce_sym prf xs = rewrite sym prf in xs
