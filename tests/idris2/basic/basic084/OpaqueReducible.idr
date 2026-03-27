module OpaqueReducible

-- A named constant using an uppercase name to avoid auto-binding in types.
MyVal : Nat
MyVal = 7

-- Mark it opaque: the type checker will not unfold MyVal
%opaque MyVal

-- At this point MyVal is Irreducible; 'test1 = Refl' would fail.

-- Restore reducibility
%reducible MyVal

-- Now MyVal is Reducible again; Refl typechecks because MyVal reduces to 7.
test1 : MyVal = 7
test1 = Refl
