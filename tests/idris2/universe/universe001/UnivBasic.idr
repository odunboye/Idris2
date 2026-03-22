module UnivBasic

-- Test basic universe stratification and cumulativity.
-- These definitions should all type-check cleanly.

-- The polymorphic identity function: id : (a : Type) -> a -> a
-- The Pi type has universe max(u_a, u_a) where a : Type u_a.
myId : (a : Type) -> a -> a
myId a x = x

-- Const function: types from (potentially) different universe levels.
myConst : (a : Type) -> (b : Type) -> a -> b -> a
myConst a b x y = x

-- Higher-order: function type is at a higher universe than its argument types.
polyApply : ((a : Type) -> a -> a) -> (b : Type) -> b -> b
polyApply f b x = f b x

-- Type of a Pi binder: (a : Type) -> a is itself a Type
idType : Type
idType = (a : Type) -> a -> a

-- Nested Pi types
flipType : Type
flipType = (a : Type) -> (b : Type) -> (c : Type) -> (a -> b -> c) -> b -> a -> c

-- A value to confirm the module compiled
result : String
result = "universe001: basic stratification OK"
