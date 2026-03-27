module PatSyn

data UnitType = MkUnit

-- Test: use constructor directly
testUnit : UnitType -> Int
testUnit MkUnit = 42

main : IO ()
main = printLn (testUnit MkUnit)
