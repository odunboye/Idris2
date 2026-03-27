module PatSyn

-- Simple pattern synonym
pattern Unit = MkUnit

data UnitType = MkUnit

-- Test using the pattern synonym
testUnit : UnitType -> Int
testUnit Unit = 42
testUnit _ = 0

main : IO ()
main = printLn (testUnit MkUnit)
