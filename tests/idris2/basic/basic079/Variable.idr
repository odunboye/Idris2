module Variable

import Data.Vect

-- %variable n1 n2 ... : T
-- Registers generalizable variable names with an explicit kind annotation.
-- Free occurrences of the declared names in subsequent type signatures are
-- auto-bound as implicit Pi binders with the declared type (rig top so they
-- are also usable in function bodies).

%variable n : Nat
%variable a b : Type

-- n and a both appear free — auto-bound as {n : Nat} {a : Type}
myHead : Vect (S n) a -> a
myHead (x :: _) = x

-- Only n appears free — auto-bound as {n : Nat}
zeros : Vect n Nat
zeros = replicate n 0   -- n accessible in body because rig is top

-- a and b both appear free — auto-bound as {a : Type} {b : Type}
myPair : a -> b -> (a, b)
myPair x y = (x, y)

-- Multiple variables, mixed
mapVec : (a -> b) -> Vect n a -> Vect n b
mapVec f [] = []
mapVec f (x :: xs) = f x :: mapVec f xs

main : IO ()
main = do
  let v : Vect 3 String := ["one", "two", "three"]
  putStrLn $ myHead v
  putStrLn $ show (zeros {n = 4})
  let p = myPair True (the Nat 42)
  putStrLn $ show p
  let v2 : Vect 3 Nat := [1, 2, 3]
  putStrLn $ show (mapVec (* 2) v2)
  putStrLn "OK"
