module UnivLib

-- A small library exporting universe-polymorphic definitions.
-- After compilation this module's universe levels are serialised to TTC;
-- UnivLibUser.idr imports it and exercises the round-tripped levels.

public export
data MyBool : Type where
  MyTrue  : MyBool
  MyFalse : MyBool

public export
data MyMaybe : Type -> Type where
  MyNothing : MyMaybe a
  MyJust    : a -> MyMaybe a

-- Universe-polymorphic identity: a : Type (implicit level via UVar).
export
myId : (a : Type) -> a -> a
myId _ x = x

-- Two arguments at (potentially) different levels.
export
myConst : (a : Type) -> (b : Type) -> a -> b -> a
myConst _ _ x _ = x

-- Returns a type — the result is itself in a higher universe.
export
myMaybeType : Type -> Type
myMaybeType a = MyMaybe a
