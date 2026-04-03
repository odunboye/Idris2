module UnivLibUser

import UnivLib

-- Tests that universe levels survive TTC serialisation and can be used
-- correctly in a downstream module.

-- Basic usage of imported definitions at ground types.
v1 : MyBool
v1 = myId MyBool MyTrue

v2 : MyBool
v2 = myConst MyBool MyBool MyFalse MyTrue

-- Passing an imported type constructor as a value (uses myMaybeType).
wrappedBool : Type
wrappedBool = myMaybeType MyBool

-- Explicit universe annotation in the importing module still works.
inType1 : Type 1
inType1 = Type 0

-- The hierarchy enforcement applies to imported-module context too.
failing "Universe level error"
  badInImporter : Type 0
  badInImporter = Type 0
