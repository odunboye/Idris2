module RewriteRule

import Data.Vect

-- Demonstrate %rewrite: promote propositional equality to definitional.
--
-- n + 0 = n is propositionally true (by induction on n) but NOT
-- definitionally true, because (+) recurses on the first argument and
-- cannot reduce when n is a variable.  After %rewrite "plusZeroRight",
-- the conversion checker rewrites n + 0 to n, so Refl typechecks.

plusZeroRight : (n : Nat) -> n + 0 = n
plusZeroRight 0     = Refl
plusZeroRight (S n) = cong S (plusZeroRight n)

%rewrite "plusZeroRight"

-- Without %rewrite this would be a type error: n + 0 /= n definitionally.
-- With %rewrite the conversion checker applies the transform and accepts Refl.
testRefl : (n : Nat) -> n + 0 = n
testRefl _ = Refl

-- %rewrite also enables the equation to be used as a cast.
-- coerce uses the definitional equality to substitute types.
coerced : Vect (n + 0) Nat -> Vect n Nat
coerced xs = xs  -- accepted because n + 0 = n definitionally after %rewrite

main : IO ()
main = do
  putStrLn "plusZeroRight: n + 0 = n (propositionally)"
  putStrLn "%rewrite promotes it to definitional equality"
  putStrLn "testRefl _ = Refl  -- typechecks (n + 0 = n definitional)"
  putStrLn "coerced xs = xs    -- typechecks (Vect (n+0) Nat = Vect n Nat)"
  putStrLn "OK"
