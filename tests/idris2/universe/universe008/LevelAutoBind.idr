module LevelAutoBind

-- Regression test: lzero, lsuc, lmax must NOT be auto-bound as fresh
-- implicit type variables when they appear in a type signature.
-- Before the fix, `f : Wrap lzero Nat` would silently become
-- `f : {lzero : Level} -> Wrap lzero Nat`, shadowing the global.

data Wrap : Level -> Type -> Type where
  MkWrap : {l : Level} -> {a : Type l} -> a -> Wrap l a

-- lzero in type position: must refer to the global, not a fresh binder.
wrapAtZero : Wrap lzero Nat
wrapAtZero = MkWrap {l = lzero} {a = Nat} 0

-- lsuc in type position: must refer to the global combinator.
wrapAtOne : Wrap (lsuc lzero) Type
wrapAtOne = MkWrap {l = lsuc lzero} {a = Type lzero} Nat

-- lmax in type position: must refer to the global function.
wrapAtMax : (l1, l2 : Level) -> Type (lmax l1 l2) -> Wrap (lmax l1 l2) (Type (lmax l1 l2))
wrapAtMax l1 l2 a = MkWrap {l = lmax l1 l2} {a = Type (lmax l1 l2)} a

-- Confirm that the wrapped values have the expected monomorphic types
-- (not `{lzero : Level} -> Wrap lzero Nat`, etc.)
checkZero : Wrap lzero Nat
checkZero = wrapAtZero

checkOne : Wrap (lsuc lzero) Type
checkOne = wrapAtOne
