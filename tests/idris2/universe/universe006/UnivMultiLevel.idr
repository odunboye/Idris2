module UnivMultiLevel

-- Tests for polymorphic functions used at multiple universe levels in the
-- same program.
--
-- Key observation: a binder typed with unannotated `Type` uses a fresh UVar
-- that stays in memory as a UVar for same-file calls (and becomes UZero only
-- after TTC serialisation).  A binder typed with explicit `Type k` always
-- uses a concrete level.  This affects how strictly levels are checked.

-- -----------------------------------------------------------------------
-- Implicit-level identity (UVar binder): flexible within same file
-- -----------------------------------------------------------------------

myId : (a : Type) -> a -> a
myId _ x = x

data MyBool : Type where
  MyTrue  : MyBool
  MyFalse : MyBool

-- Ground-type usage: fully concrete, works.
v1 : MyBool
v1 = myId MyBool MyTrue

-- Passing unannotated `Type` as the `a` argument.
-- `Type` produces a fresh UVar; the UVar-based expected type is optimistic
-- (level check returns Nothing), so this is accepted.
typeOfBool : Type
typeOfBool = myId Type MyBool

-- -----------------------------------------------------------------------
-- Explicit-level-0 identity: strict at level 0
-- -----------------------------------------------------------------------

myId0 : (a : Type 0) -> a -> a
myId0 _ x = x

-- Level-0 identity works fine with a ground type (MyBool : Type 0).
v2 : MyBool
v2 = myId0 MyBool MyTrue

-- Passing explicit `Type 0` to a level-0 slot is correctly rejected:
-- Type 0 has type Type 1, but the slot expects something of type Type 0.
failing "Universe level error"
  cannotLiftType : MyBool
  cannotLiftType = myId0 (Type 0) MyTrue

-- -----------------------------------------------------------------------
-- Level-1 functions: accepting and returning types
-- -----------------------------------------------------------------------

-- A function typed at level 1: takes a Type 1, returns it as Type 1.
typeId1 : (a : Type 1) -> Type 1
typeId1 a = a

-- Type 0 lives in Type 1, so passing it here is valid.
v3 : Type 1
v3 = typeId1 (Type 0)

-- Type 1 lives in Type 2, not Type 1: correctly rejected.
failing "Universe level error"
  cannotSelfContainType1 : Type 1
  cannotSelfContainType1 = typeId1 (Type 1)

-- -----------------------------------------------------------------------
-- Mixed: level-0 and level-1 values coexist in the same program
-- -----------------------------------------------------------------------

-- A level-0 concrete value and a level-1 type value in the same file.
ground : MyBool
ground = MyTrue

lifted : Type 1
lifted = Type 0

-- Both usable independently without interference.
useGround : MyBool
useGround = myId0 MyBool ground

useLifted : Type 1
useLifted = lifted
