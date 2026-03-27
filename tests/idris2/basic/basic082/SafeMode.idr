-- This should fail in safe mode

module SafeMode

%terminating
foo : Nat -> Nat
foo n = n
