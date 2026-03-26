-- Basic test for Row 41: Guarded Recursion
-- Tests the Data.Guarded library with all the new features

import Data.Guarded

%default total

-- Test 1: Clock primitive type
clockTest : Clock -> Clock
clockTest k = k

-- Test 2: Later type and next constructor
laterTest : (k : Clock) -> Later k Nat
laterTest k = next k 42

-- Test 3: force function
forceTest : (k : Clock) -> Nat
forceTest k = force (next k 42)

-- Test 4: Functor instance (map)
doubleLater : (k : Clock) -> Later k Nat -> Later k Nat
doubleLater k = map (2 *)

-- Test 5: Applicative instance (pure and <*>)
addLater : (k : Clock) -> Later k Nat -> Later k Nat -> Later k Nat
addLater k la lb = pure (+) <*> la <*> lb

-- Test 6: Monad instance (>>=)
chainLater : (k : Clock) -> Later k Nat -> Later k Nat
chainLater k la = do
  n <- la
  pure (n + 1)

-- Test 7: liftA2
multiplyLater : (k : Clock) -> Later k Nat -> Later k Nat -> Later k Nat
multiplyLater k = liftA2 (*)

-- Test 8: zip
pairLater : (k : Clock) -> Later k Nat -> Later k String -> Later k (Nat, String)
pairLater k = zip

-- Test 9: fix combinator
ones : (k : Clock) -> Later k Nat
ones k = fix k (\rec => next k 1)

-- Test 10: Boolean operations
testAnd : (k : Clock) -> Later k Bool -> Later k Bool -> Later k Bool
testAnd k = andLater

-- Test 11: delayN
delayed42 : (k : Clock) -> Later k Nat
delayed42 k = delayN 3 42

-- Test 12: liftOp
addOp : (k : Clock) -> Later k Nat -> Later k Nat -> Later k Nat
addOp k = liftOp (+)

-- Main placeholder
main : IO ()
main = putStrLn "All Data.Guarded tests passed!"
