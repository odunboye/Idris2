module UnivLevelBinders

-- Test: explicit {l : Level} binder syntax for universe polymorphism.
-- Level-typed implicit binders are automatically erased and their values
-- are resolved via the UVar mechanism.

data Level : Type where
  LZero : Level
  LSuc : Level -> Level

lzero : Level
lzero = LZero

lsuc : Level -> Level
lsuc = LSuc

lmax : Level -> Level -> Level
lmax LZero r = r
lmax l LZero = l
lmax (LSuc l) (LSuc r) = LSuc (lmax l r)

data MyNat : Type where
  Z : MyNat
  S : MyNat -> MyNat

-- Basic: single level parameter
myId : {l : Level} -> (a : Type l) -> a -> a
myId a x = x

-- Calling myId: the {l : Level} implicit is auto-solved
test1 : MyNat
test1 = myId MyNat (S Z)

-- Multiple level parameters
myConst : {l1 : Level} -> {l2 : Level} -> (a : Type l1) -> (b : Type l2) -> a -> b -> a
myConst a b x y = x

test2 : MyNat
test2 = myConst MyNat MyNat Z (S Z)

-- Level parameter with lsuc
myId1 : {l : Level} -> (a : Type (lsuc l)) -> a -> a
myId1 a x = x

-- Explicit Level arguments (e.g. on functions operating on Level values)
-- should NOT be erased.
levelSucc : Level -> Level
levelSucc = LSuc
