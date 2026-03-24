||| Propositional truncation (squash types).
|||
||| `Squash a`, written `‖a‖`, witnesses that `a` is inhabited without
||| retaining which inhabitant was given.  The value inside is irrelevant:
||| the type checker uses it to verify existence, but it is erased at
||| runtime and cannot be extracted into a computationally relevant position.
|||
||| This gives a lightweight form of proof irrelevance: no Idris program
||| can distinguish two values of type `‖a‖` by their internal witness.
|||
||| # Usage
||| ```idris
||| import Data.Squash
|||
||| -- Wrap: any `a` gives `‖a‖`
||| ex1 : ‖Nat‖
||| ex1 = squash 42
|||
||| -- Map: transform inside without extracting
||| ex2 : ‖String‖
||| ex2 = map show ex1
|||
||| -- The witness cannot escape:
||| -- extract : ‖a‖ -> a          -- REJECTED by IrrelevantUsed check
||| -- extract (MkSquash x) = x    -- irrelevant `x` in relevant position
||| ```
module Data.Squash

%default total

---------------------------------------------------------------------------
-- The type
---------------------------------------------------------------------------

||| The squash (propositional truncation) of `a`.
||| Inhabitants exist iff `a` is inhabited, but the witness is irrelevant.
public export
data Squash : Type -> Type where
  ||| Introduce a squashed value.  The argument is irrelevant: it is
  ||| erased at runtime and may not be used in any relevant position.
  MkSquash : .(x : a) -> Squash a

---------------------------------------------------------------------------
-- Introduction
---------------------------------------------------------------------------

||| Squash a value.  The result is proof that `a` is inhabited.
public export
squash : a -> Squash a
squash x = MkSquash x

---------------------------------------------------------------------------
-- Elimination  (restricted — only into Squash itself)
---------------------------------------------------------------------------

||| Map a function over a squashed value.
||| The result stays squashed, so no information escapes.
||| Both the function and the witness are used only inside a new MkSquash
||| (irrelevant argument position), so the IrrelevantUsed check passes.
public export
squashMap : (a -> b) -> Squash a -> Squash b
squashMap f (MkSquash x) = MkSquash (f x)

---------------------------------------------------------------------------
-- Functor / Applicative
---------------------------------------------------------------------------

public export
Functor Squash where
  map = squashMap

public export
Applicative Squash where
  pure      = squash
  MkSquash f <*> MkSquash x = MkSquash (f x)

---------------------------------------------------------------------------
-- Conversion
---------------------------------------------------------------------------

||| Any decidable proposition can be squashed.
public export
fromDec : Dec a -> Squash (Either a (a -> Void))
fromDec (Yes p) = MkSquash (Left  p)
fromDec (No  n) = MkSquash (Right n)
