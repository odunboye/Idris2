module Main

import Data.Squash

-- Basic introduction: ‖A‖ syntax and squash
s1 : ‖Nat‖
s1 = squash 5

-- Functor: map over a squashed value without escaping
s2 : ‖String‖
s2 = map show s1

-- Applicative: apply squashed function to squashed argument
s3 : ‖Nat‖
s3 = squash (\x => x + 1) <*> squash 99

-- fromDec: turn a decision into a squashed Either
s4 : ‖Either Nat (Nat -> Void)‖
s4 = fromDec (Yes 7)

-- Pattern match: discarding the irrelevant witness is allowed
isInhabited : ‖a‖ -> String
isInhabited (MkSquash _) = "inhabited"

main : IO ()
main = do
  -- f ignores the squash value entirely (proof-irrelevant use)
  putStrLn (isInhabited s1)
  putStrLn (isInhabited s2)
  putStrLn (isInhabited s3)
  putStrLn (isInhabited s4)
