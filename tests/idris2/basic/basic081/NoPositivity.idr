-- Test for [noPositivity] data option

module NoPositivity

-- This would normally fail the positivity check
-- because the function type contains the type itself
data Weird : Type where [noPositivity]
  MkWeird : ((Weird -> Bool) -> Bool) -> Weird

-- Using the type
weirdValue : Weird
weirdValue = MkWeird (\f => f weirdValue)

main : IO ()
main = printLn "NoPositivity test passed"
