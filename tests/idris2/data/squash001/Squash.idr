module Main

import Data.Squash

-- Test parsing of squash type
s1 : ‖ Nat ‖
s1 = squash 5

-- Test usage in type signatures
f : ‖ Nat ‖ -> String
f x = "Squashed!"

main : IO ()
main = do
  putStrLn (f s1)
