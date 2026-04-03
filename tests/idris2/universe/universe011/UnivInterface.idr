module UnivInterface

-- Test: interfaces with universe polymorphism.
-- Interfaces desugar to records + search, and the universe level system
-- should handle them correctly.

data Level : Type where
  LZero : Level
  LSuc : Level -> Level

lzero : Level
lzero = LZero

lsuc : Level -> Level
lsuc = LSuc

data MyNat : Type where
  Z : MyNat
  S : MyNat -> MyNat

data MyBool : Type where
  MyTrue : MyBool
  MyFalse : MyBool

-- Basic interface
interface MyEq a where
  myEq : a -> a -> MyBool

MyEq MyNat where
  myEq Z Z = MyTrue
  myEq (S k) (S j) = myEq k j
  myEq _ _ = MyFalse

-- Interface constraint
eqTest : MyEq a => a -> a -> MyBool
eqTest x y = myEq x y

test1 : MyBool
test1 = eqTest Z (S Z)

-- Interface with Type in method signatures
interface MyTypeable a where
  myTypeOf : a -> Type

MyTypeable MyNat where
  myTypeOf _ = MyNat

-- Interface on higher-kinded types
interface MyKind (f : Type -> Type) where
  myKindOf : f a -> Type

data MyBox : Type -> Type where
  MkMyBox : a -> MyBox a

MyKind MyBox where
  myKindOf (MkMyBox _) = MyNat

test2 : Type
test2 = myKindOf (MkMyBox Z)

-- Universe-polymorphic function using interface constraint
myIdEq : MyEq a => a -> a -> MyBool
myIdEq x y = myEq x y
