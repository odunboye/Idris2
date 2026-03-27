module Opaque

-- A value marked opaque should still be computable at runtime.
mySecret : Nat
mySecret = 42

%opaque mySecret

-- Runtime computation still works even though the definition is irreducible
-- in the type-checker.
main : IO ()
main = printLn mySecret
