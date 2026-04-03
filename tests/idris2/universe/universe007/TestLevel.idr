module TestLevel

-- lzero, lsuc, lmax are first-class Level values
test1 : Level
test1 = lzero

test2 : Level
test2 = lsuc lzero

test3 : Level
test3 = lmax (lsuc lzero) lzero

-- Type (lsuc lzero) works for Type 1 values
test4 : Type (lsuc lzero)
test4 = String

-- Level-polymorphic identity
LevelId : (l : Level) -> Type l -> Type l
LevelId _ a = a

-- Type 0 and Type (lzero) should be the same
-- (both elaborate to TType fc UZero)
test5 : Type lzero
test5 = Bool

-- lsuc l for variable l
test6 : (l : Level) -> Type (lsuc l)
test6 l = Type l

main : IO ()
main = putStrLn "Level : Type works!"
