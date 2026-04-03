module TestLevel

-- Tests for Level : Type as a first-class type.
-- Level, lzero, lsuc, lmax are provided by the Prelude.

-- Basic Level values
test1 : Level
test1 = lzero

test2 : Level
test2 = lsuc lzero

test3 : Level
test3 = lmax (lsuc lzero) lzero   -- normalises to lsuc lzero

-- Type lzero is the same universe as Type 0
test4 : Type lzero
test4 = Nat

-- Type (lsuc lzero) = Type 1; a Type (e.g. Nat) lives there
test5 : Type (lsuc lzero)
test5 = Nat

-- lsuc l for a bound variable l
typeAtSucc : (l : Level) -> Type (lsuc l)
typeAtSucc l = Type l

-- lmax of two level variables (explicit annotation avoids inference gap)
typeAtMax : (l1, l2 : Level) -> Type (lmax l1 l2) -> Type (lmax l1 l2)
typeAtMax l1 l2 a = a
