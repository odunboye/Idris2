||| Propositional truncation (squash types).
|||
||| `Squash a`, written `‖a‖`, witnesses that `a` is inhabited without
||| retaining which inhabitant was given.  The value inside is logically
||| irrelevant: it is erased at runtime and may not be used in any
||| computationally relevant position.
|||
||| ## Definitional proof irrelevance
|||
||| Because `MkSquash` takes a `.(x : a)` argument (an *irrelevant* Pi binder,
||| not merely an erased one), the kernel's Row-42 check (`allExplicitErased`)
||| classifies `Squash` as *definitionally proof-irrelevant*.  This means the
||| conversion checker treats any two values of type `‖a‖` as definitionally
||| equal — without inspecting their witnesses — enabling `proofIrrelevance`
||| to be proved by `Refl`:
|||
||| ```idris
||| proofIrrelevance : (p : ‖a‖) -> (q : ‖a‖) -> p = q
||| proofIrrelevance p q = Refl   -- accepted because p ≡ q definitionally
||| ```
|||
||| ## Difference between `.(x : a)` and `(0 x : a)`
|||
||| | Annotation      | Runtime | Type-level | DPI |
||| |-----------------|---------|------------|-----|
||| | `(0 x : a)`     | erased  | visible    | No  |
||| | `.(x : a)`      | erased  | invisible  | Yes |
|||
||| The `.(x : a)` (irrelevant Pi) binder is strictly stronger: `x` is
||| invisible even at the type level, so no dependent function can distinguish
||| two inhabitants — which is exactly what is needed for DPI to be sound.
|||
||| ## Usage
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
||| -- Propositional equality of any two squash values
||| samePrf : (p : ‖Nat‖) -> (q : ‖Nat‖) -> p = q
||| samePrf p q = proofIrrelevance p q
|||
||| -- The witness cannot escape:
||| -- extract : ‖a‖ -> a          -- REJECTED (irrelevant in relevant position)
||| -- extract (MkSquash x) = x    -- REJECTED (x is irrelevant)
||| ```
module Data.Squash

%default total

---------------------------------------------------------------------------
-- The type
---------------------------------------------------------------------------

||| The squash (propositional truncation) of `a`.
||| Inhabitants exist iff `a` is inhabited, but the witness is irrelevant.
|||
||| The constructor argument is an *irrelevant* Pi binder `.(x : a)`, which
||| makes `Squash` definitionally proof-irrelevant in the kernel (Row 42).
public export
data Squash : Type -> Type where
  ||| Introduce a squashed value.
  ||| The argument uses an irrelevant Pi binder `.(x : a)`: it is erased at
  ||| runtime AND invisible at the type level, enabling definitional proof
  ||| irrelevance for the whole type.
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
-- Definitional and propositional proof irrelevance
---------------------------------------------------------------------------

||| Any two values of type `Squash a` are propositionally equal.
|||
||| This is a *theorem* (not a postulate): it is proved by `Refl` because
||| the kernel's Row-42 mechanism makes `Squash` definitionally proof-irrelevant
||| — any two `Squash a` terms convert without inspecting their witnesses.
|||
||| ```idris
||| p q : ‖Nat‖
||| proofIrrelevance p q : p === q   -- holds for any p, q
||| ```
export
proofIrrelevance : (p : Squash a) -> (q : Squash a) -> p = q
proofIrrelevance p q = Refl

---------------------------------------------------------------------------
-- ProofIrrelevant interface
---------------------------------------------------------------------------

||| A type is *proof-irrelevant* if any two of its inhabitants are
||| propositionally equal.  This is the logical (propositional) counterpart
||| of the kernel's definitional proof irrelevance.
|||
||| Instances should only be provided for types that are genuinely
||| proof-irrelevant — either by kernel support (like `Squash`) or by
||| explicit proof (like `Unit`).
public export
interface ProofIrrelevant (0 a : Type) where
  ||| Prove that any two inhabitants of `a` are propositionally equal.
  proofIrrel : (p : a) -> (q : a) -> p = q

||| `Squash a` is proof-irrelevant: this follows directly from
||| `proofIrrelevance`, which is a theorem proved by `Refl`.
export
[SquashProofIrrelevant] ProofIrrelevant (Squash a) where
  proofIrrel = proofIrrelevance

||| `Unit` (the unit type `()`) is proof-irrelevant: its only inhabitant
||| is `MkUnit`, so any two values are trivially equal.
[UnitProofIrrelevant] ProofIrrelevant Unit where
  proofIrrel () () = Refl

---------------------------------------------------------------------------
-- Conversion
---------------------------------------------------------------------------

||| Any decidable proposition can be squashed.
public export
fromDec : Dec a -> Squash (Either a (a -> Void))
fromDec (Yes p) = MkSquash (Left  p)
fromDec (No  n) = MkSquash (Right n)
