module NeverDefined

-- This type signature is never followed by a definition.
-- The compiler should warn: "ghost was declared but never defined."
ghost : Nat -> Nat

main : IO ()
main = putStrLn "ok"
