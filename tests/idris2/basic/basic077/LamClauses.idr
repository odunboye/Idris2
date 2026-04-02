||| Row 9 — Multi-clause pattern matching lambdas
|||
||| \{ p1 p2 => e1 ; p3 p4 => e2 } desugars to a nested lambda over fresh
||| names that immediately case-splits on the right-nested pair of arguments.
module LamClauses

-- 1. Single argument (degenerate — same as \case)
natName : Nat -> String
natName = \{ Z => "zero" ; (S Z) => "one" ; (S (S _)) => "many" }

-- 2. Two arguments
myAdd : Nat -> Nat -> Nat
myAdd = \{ Z m => m ; (S n) m => S (myAdd n m) }

-- 3. Three arguments
choose : Nat -> Nat -> Nat -> Nat
choose = \{ Z Z k => k ; Z j _ => j ; i _ _ => i }

-- 4. Works as a value — assigned to a typed binding
myMax : Nat -> Nat -> Nat
myMax = \{ Z m => m ; n Z => n ; (S n') (S m') => S (myMax n' m') }

main : IO ()
main = do
  -- 1. Single-arg
  putStrLn (natName 0)
  putStrLn (natName 1)
  putStrLn (natName 5)
  -- 2. Two-arg
  printLn (myAdd 2 3)
  -- 3. Three-arg
  printLn (choose 0 0 7)
  printLn (choose 0 4 7)
  printLn (choose 5 4 7)
  -- 4. Three-clause two-arg
  printLn (myMax 3 7)
  printLn (myMax 9 4)
