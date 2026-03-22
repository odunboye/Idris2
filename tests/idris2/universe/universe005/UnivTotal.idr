module UnivTotal

%default total

-- Universe hierarchy enforcement must work transparently alongside the
-- totality checker.  These are orthogonal features; neither should break
-- the other.

-- -----------------------------------------------------------------------
-- Positive: total definitions with universe-level annotations
-- -----------------------------------------------------------------------

-- Total identity at implicit universe level.
myId : (a : Type) -> a -> a
myId _ x = x

-- A data type that is total by construction.
data MyNat : Type where
  Z : MyNat
  S : MyNat -> MyNat

-- Recursive (structural, hence total) definition.
add : MyNat -> MyNat -> MyNat
add Z     m = m
add (S n) m = S (add n m)

-- Explicit universe level annotation: Type 0 in Type 1 is fine.
concreteType : Type 1
concreteType = Type 0

-- Level 2 accepts level 1.
higherType : Type 2
higherType = Type 1

-- -----------------------------------------------------------------------
-- Negative: universe errors are still caught under %default total
-- -----------------------------------------------------------------------

-- Type 0 : Type 0 is rejected even with %default total.
failing "Universe level error"
  badTotal : Type 0
  badTotal = Type 0

-- Type 1 : Type 1 is also rejected.
failing "Universe level error"
  badTotal2 : Type 1
  badTotal2 = Type 1
