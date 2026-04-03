module UnivDataCheck

-- Test: data type constructor argument universe checking.

-- This should succeed: Nat-like data at Type 0 with Type 0 arguments.
data MyNat : Type where
  MZ : MyNat
  MS : MyNat -> MyNat

-- This should succeed: a data type at Type 1 holding a Type 0 value.
data Wrap1 : Type 1 where
  MkWrap1 : Type -> Wrap1

-- This should fail: a data type at Type 0 trying to store Type 0.
-- Type 0 : Type 1, so the argument lives at universe 1 which exceeds
-- the data type's universe 0.
failing "Universe level error"
  data Bad0 : Type 0 where
    MkBad0 : Type 0 -> Bad0

-- This should succeed: data type at Type 1, argument is Type 0 : Type 1.
data Good1 : Type 1 where
  MkGood1 : Type 0 -> Good1

-- This should succeed: a simple parameterised type.
data MyList : Type -> Type where
  Nil  : MyList a
  Cons : a -> MyList a -> MyList a

-- This should succeed: identity wrapper.
data Id : Type -> Type where
  MkId : a -> Id a
