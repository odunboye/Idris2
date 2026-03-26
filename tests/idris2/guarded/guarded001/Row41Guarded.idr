-- Row 41: Guarded Recursion / Clock Variables
-- Based on Atkey & McBride (2013)
--
-- This file demonstrates the intended syntax and behavior for guarded recursion.
-- It serves as a specification for the implementation.

%default total

-- =============================================================================
-- BASIC CLOCK TYPES AND LATER MODALITY
-- =============================================================================

-- The Clock type is a new primitive sort
-- Clock : Type

-- Later modality: ▶κ A means "A is available after one tick on clock κ"
-- Later : (κ : Clock) -> Type -> Type

-- Introduction: next wraps a value in the later modality
-- next : (κ : Clock) -> A -> Later κ A

-- Elimination via tick abstraction/application:
-- tick abstraction:  \(tick κ) => e  or  λ̲κ. e
-- tick application:  f @(tick κ)   or  f @κ

-- =============================================================================
-- EXAMPLE 1: Basic Stream with Guarded Recursion
-- =============================================================================

-- Stream type with guarded tail
-- The tail is only available "later" on clock κ
record Stream (κ : Clock) (A : Type) where
  constructor MkStream
  head : A
  tail : Later κ (Stream κ A)

-- Infix cons operator
(:::>) : A -> Later κ (Stream κ A) -> Stream κ A
(:::>) = MkStream

-- Productive infinite stream of ones
-- No assert_total needed - guarded recursion ensures productivity
ones : (κ : Clock) -> Stream κ Nat
ones κ = MkStream 1 (next κ (ones κ))

-- =============================================================================
-- EXAMPLE 2: Stream Operations (Compositional)
-- =============================================================================

-- Map over streams - compositional!
-- The recursive call is guarded by next
mapStream : (a -> b) -> Stream κ a -> Stream κ b
mapStream f s = MkStream (f s.head) (next κ (mapStream f (forceLater s.tail)))
  where
    -- forceLater : Later κ A -> A  (available via tick application)
    forceLater : Later κ (Stream κ a) -> Stream κ a
    forceLater la = la @(tick κ)

-- Zip two streams together
zipWithStream : (a -> b -> c) -> Stream κ a -> Stream κ b -> Stream κ c
zipWithStream f s1 s2 = 
  MkStream (f s1.head s2.head)
           (next κ (zipWithStream f (s1.tail @(tick κ)) (s2.tail @(tick κ))))

-- The fibonacci stream
fibs : (κ : Clock) -> Stream κ Nat
fibs κ = MkStream 0 (next κ (fibs' κ))
  where
    fibs' : (κ : Clock) -> Stream κ Nat
    fibs' κ = MkStream 1 (next κ (zipWithStream (+) (fibs κ) (fibs' κ)))

-- =============================================================================
-- EXAMPLE 3: From Guarded to Coinductive (Removing Clocks)
-- =============================================================================

-- We can turn a clocked stream into a regular coinductive stream
-- by hiding the clock behind Inf

-- delay : ((κ : Clock) -> Stream κ A) -> Inf (Stream A)
-- delay s = Delay (s _)  -- _ infers a fresh clock

-- Conversely, we can extract from a coinductive stream
-- using a specific clock
-- forceClock : (κ : Clock) -> Inf (Stream A) -> Stream κ A

-- =============================================================================
-- EXAMPLE 4: Guarded Fixpoint
-- =============================================================================

-- The fix combinator for guarded recursion
-- fix : (κ : Clock) -> (Later κ A -> A) -> A

-- Using fix explicitly
countFrom : (κ : Clock) -> Nat -> Stream κ Nat
countFrom κ n = fix κ (\later => 
  MkStream n (next κ (countFrom κ (S n))))

-- =============================================================================
-- EXAMPLE 5: N-ary Guarded Types (Productive Functions)
-- =============================================================================

-- Guarded function type: produces result "later"
GFun : Clock -> Type -> Type -> Type
GFun κ a b = a -> Later κ b

-- Kleisli composition for guarded functions
-- (composing productive operations)
kcompose : (b -> Later κ c) -> (a -> Later κ b) -> (a -> Later κ c)
kcompose f g a = next κ (f (g a @(tick κ)) @(tick κ))

-- =============================================================================
-- EXAMPLE 6: Higher-Order Guarded Types
-- =============================================================================

-- Guarded stream of streams
streamOfStreams : (κ : Clock) -> Stream κ (Stream κ Nat)
streamOfStreams κ = 
  let s1 = ones κ
      s2 = countFrom κ 0
  in MkStream s1 (next κ (MkStream s2 (next κ (streamOfStreams κ))))

-- =============================================================================
-- EXAMPLE 7: Mutual Guarded Recursion
-- =============================================================================

mutual
  -- Even numbers stream
  evens : (κ : Clock) -> Stream κ Nat
  evens κ = MkStream 0 (next κ (evens' κ))
  
  -- Odd numbers stream (defined via evens)
  odds : (κ : Clock) -> Stream κ Nat
  odds κ = MkStream 1 (next κ (odds' κ))
  
  evens' : (κ : Clock) -> Stream κ Nat
  evens' κ = mapStream S (odds κ)
  
  odds' : (κ : Clock) -> Stream κ Nat
  odds' κ = mapStream S (evens κ)

-- =============================================================================
-- EXAMPLE 8: Type-safe unfold with guarded recursion
-- =============================================================================

-- Unfold produces a productive stream from a seed
unfold : (s -> (a, Later κ s)) -> s -> Stream κ a
unfold f seed = 
  let (a, nextSeed) = f seed
  in MkStream a (next κ (unfold f (nextSeed @(tick κ))))

-- Example: Generate powers of 2
powersOf2 : (κ : Clock) -> Stream κ Nat
powersOf2 κ = unfold (\n => (n, next κ (S n * S n))) 1

-- =============================================================================
-- EXAMPLE 9: Incorrect (Non-Productive) Definitions That Should Fail
-- =============================================================================

-- These definitions should be rejected by the productivity checker:

{-
-- ERROR: Unguarded recursive call
badOnes : (κ : Clock) -> Stream κ Nat
badOnes κ = MkStream 1 (badOnes κ)  -- No next wrapper!

-- ERROR: Clock escape in result type
badEscape : (κ : Clock) -> Later κ Nat
badEscape κ = next κ 42  -- κ appears in result!

-- ERROR: Unguarded via pattern match
badMatch : (κ : Clock) -> Stream κ Nat -> Stream κ Nat
badMatch κ s = MkStream s.head (badMatch κ s)  -- tail recursion not guarded
-}

-- =============================================================================
-- MAIN
-- =============================================================================

takeStream : Nat -> Stream κ a -> List a
takeStream Z _ = []
takeStream (S n) s = s.head :: takeStream n (s.tail @(tick κ))

main : IO ()
main = do
  putStrLn "Guarded recursion examples loaded successfully!"
  putStrLn "This module demonstrates the intended syntax for Row 41."
