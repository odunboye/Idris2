-- Sub-problem A: automatic sym for rewrite.
--
-- When prf : lt = rt and the goal contains rt (not lt),
-- `rewrite prf` should automatically use `sym prf`.
-- Before this fix the user had to write `rewrite sym prf in xs` manually.
module AutoSym

import Data.Vect

myLemma : (n : Nat) -> n + 0 = n
myLemma 0 = Refl
myLemma (S k) = rewrite myLemma k in Refl

-- Goal is `Vect n a`; prf has `n+0` on LHS, `n` on RHS.
-- Auto-sym: rewrite prf -> internally uses sym prf, finding `n` in goal.
coerce_auto : {n : Nat} -> (0 prf : n + 0 = n) -> Vect (n + 0) a -> Vect n a
coerce_auto prf xs = rewrite prf in xs

-- Explicit sym still works too.
coerce_sym : {n : Nat} -> (0 prf : n + 0 = n) -> Vect (n + 0) a -> Vect n a
coerce_sym prf xs = rewrite sym prf in xs

-- Rewriting FROM the type of xs TO a concrete expected type (forward auto-sym).
-- prf : n = S m, xs : Vect n a -> result Vect (S m) a.
-- Auto-sym finds `S m` (RHS) in the goal `Vect (S m) a`.
transportVect : {n, m : Nat} -> (prf : n = S m) -> Vect n a -> Vect (S m) a
transportVect prf xs = rewrite prf in xs

-- Intermediate binding with concrete expected type works too.
myHead : {n : Nat} -> Vect (S n) a -> a
myHead (x :: _) = x

withConcrete : {n, m : Nat} -> (prf : n = S m) -> Vect n a -> a
withConcrete prf xs =
    let ys : Vect (S m) a := rewrite prf in xs
    in myHead ys

-- Rewrite in argument position where the expected type has a meta (?k).
-- myHead : Vect (S ?k) a -> a; rewrite prf fills ?k = m.
-- Requires replaceWithUnify (unification-based match) in strategy 2.
withMeta : {n, m : Nat} -> (prf : n = S m) -> Vect n a -> a
withMeta prf xs = myHead (rewrite prf in xs)
