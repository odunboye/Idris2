-- Test for %terminating and %nocoverage pragmas

module TerminationPragmas

-- Test %terminating: Ackermann function that would fail termination check
-- without the pragma (not structurally recursive in the usual sense)
%terminating
ackermann : Nat -> Nat -> Nat
ackermann Z n = S n
ackermann (S m) Z = ackermann m (S Z)
ackermann (S m) (S n) = ackermann m (ackermann (S m) n)

-- Test %nocoverage: Partial function that is intentionally not covering
%nocoverage
fromJust : Maybe a -> a
fromJust (Just x) = x
-- No Nothing case - we know it's never called with Nothing

-- Test both together
%terminating
%nocoverage
unsafeHead : List a -> a
unsafeHead (x :: xs) = x

-- Usage
main : IO ()
main = do
  printLn (ackermann 3 2)
  printLn (fromJust (Just 42))
  printLn (unsafeHead [1, 2, 3])
