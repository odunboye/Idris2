module UnivExplicitLevel

-- Test: explicit Level argument passing at call sites.

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

-- Universe-polymorphic identity with explicit level binder
myId : {l : Level} -> (a : Type l) -> a -> a
myId a x = x

-- Auto-solved: l inferred from MyNat : Type 0
test1 : MyNat
test1 = myId MyNat Z

-- Explicit level: l = lzero
test2 : MyNat
test2 = myId {l = lzero} MyNat (S Z)

-- Explicit level: l = lsuc lzero (Type : Type 1)
test3 : Type
test3 = myId {l = lsuc lzero} Type MyNat

-- Multiple level params, all auto-solved
myConst : {l1 : Level} -> {l2 : Level} -> (a : Type l1) -> (b : Type l2) -> a -> b -> a
myConst a b x y = x

test4 : MyNat
test4 = myConst MyNat MyNat Z (S Z)

-- Mixing explicit and auto-solved levels
test5 : MyNat
test5 = myConst {l1 = lzero} MyNat MyNat (S Z) Z
