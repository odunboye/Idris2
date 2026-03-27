-- Test for %noPositivity pragma on data types

module NoPositivity

-- This would normally fail the positivity check
-- because the function type contains the type itself
%noPositivity
data Weird : Type where
  MkWeird : ((Weird -> Bool) -> Bool) -> Weird

-- Using the type
weirdValue : Weird
weirdValue = MkWeird (\f => f weirdValue)

main : IO ()
main = printLn "NoPositivity test passed"
