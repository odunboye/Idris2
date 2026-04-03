module UnivRecordRetTy

-- Test: record return type annotations for universe levels.
-- record Foo : Type k where ...

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

-- Record with explicit return type: Type 1 (holds a Type value)
record TypeWrapper : Type 1 where
  constructor MkTypeWrapper
  wrapped : Type

test1 : TypeWrapper
test1 = MkTypeWrapper MyNat

-- Record without return type annotation (inferred, should work as before)
record Box (a : Type) where
  constructor MkBox
  unbox : a

test2 : Box MyNat
test2 = MkBox Z

-- Record at Type 2 holding Type 1 values
record TypeWrapper2 : Type 2 where
  constructor MkTypeWrapper2
  wrapped : Type 1

test3 : TypeWrapper2
test3 = MkTypeWrapper2 (Type 0)

-- Bad: record at Type 0 trying to store Type 0 (needs Type 1)
failing "Universe level error"
  record BadWrapper : Type 0 where
    constructor MkBadWrapper
    wrapped : Type 0
