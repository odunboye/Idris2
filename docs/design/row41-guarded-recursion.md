# Design Document: Row 41 - Guarded Recursion / Clock Variables

**Status**: Design Phase  
**Based on**: Atkey & McBride (2013) "Productive Coprogramming with Guarded Recursion"  
**Reference Implementation**: Agda's `--guarded` flag (experimental, 2.6.3+)

---

## 1. Motivation

### Current Problems

Idris 2 currently handles coinductive types through `Inf` and manual `Delay`/`Force`:

```idris
-- Current approach (Row 36 - implemented)
ones : Stream Nat
ones = 1 :: Delay ones  -- Requires syntactic guardedness check

-- Problem: Nested recursion often fails
mapS : (a -> b) -> Stream a -> Stream b
mapS f (x :: xs) = f x :: Delay (mapS f (Force xs))  -- Needs assert_total
```

### Why Guarded Recursion is Better

| Aspect | Current (`Inf`/`Delay`) | Guarded Recursion (Row 41) |
|--------|------------------------|---------------------------|
| Safety | Syntactic check, easy to bypass | Type-based, cannot cheat |
| Composition | Nested recursion problematic | Compositional via ▶κ |
| Universe levels | Works with polymorphism | No soundness issues |
| User experience | `assert_total` needed often | Truly total programming |

---

## 2. Type Theory

### 2.1 Clock Variables

Clocks are a new sort at the type level:

```
κ : Clock    -- Clock variable
```

Clocks are introduced via clock abstraction and eliminated via tick application.

### 2.2 Later Modality (▶κ)

```
Γ ⊢ A : Type ℓ       Γ ⊢ κ : Clock
---------------------------------
Γ ⊢ ▶κ A : Type ℓ
```

**Intuition**: `▶κ A` is the type of values of type `A` that are available "one time step later" on clock κ.

### 2.3 Term Constructors

#### next - Introduction

```
Γ ⊢ κ : Clock    Γ ⊢ a : A
---------------------------
Γ ⊢ next κ a : ▶κ A
```

Wraps a value in the later modality.

#### Tick Abstraction (λ̲κ. t)

```
Γ, κ : Clock ⊢ t : A    κ ∉ fv(A)  -- Clock irrelevance
------------------------------------
Γ ⊢ λ̲κ. t : ∀κ. A
```

**Important**: The result type `A` cannot depend on κ (clock irrelevance).

#### Tick Application (t @κ)

```
Γ ⊢ t : ∀κ. A    Γ ⊢ κ : Clock
-------------------------------
Γ ⊢ t @κ : A[κ/κ']
```

Forces a clock-quantified computation at a specific clock.

#### fix - Guarded Fixed Point

```
Γ ⊢ κ : Clock    Γ ⊢ f : ▶κ A -> A
-----------------------------------
Γ ⊢ fix κ f : A
```

Defines a productive recursive value. The recursive calls are guarded by ▶κ.

---

## 3. Surface Syntax

### 3.1 Types

| Construct | Syntax | Example |
|-----------|--------|---------|
| Later type | `Later κ A` or `▶κ A` | `▶κ (Stream Nat)` |
| Clock quantification | `(κ : Clock) ->` | `(κ : Clock) -> ▶κ Nat -> Nat` |
| Clock abstraction type | `forall κ. A` | `forall κ. Streamκ A` |

### 3.2 Terms

| Construct | Syntax | Desugars To |
|-----------|--------|-------------|
| next | `next κ e` | `TNext fc κ e` |
| tick lambda | `λ̲κ. e` or `\tick κ => e` | `TTickAbs fc κ e` |
| tick app | `e @κ` or `e @ tick κ` | `TTickApp fc e κ` |
| fix | `fix κ f` | `TFix fc κ f` |

### 3.3 ASCII Alternatives

For terminals without Unicode:

```idris
-- Unicode style
ones : (κ : Clock) -> Streamκ Nat
ones κ = MkStream 1 (next κ (ones κ))

-- ASCII style  
ones : (k : Clock) -> Stream k Nat
ones k = MkStream 1 (next k (ones k))

-- Alternative: keywords
ones : forall k. Stream k Nat
ones = \tick k => MkStream 1 (next k (ones @k))
```

---

## 4. Core Representation

### 4.1 New Term Constructors (Core/TT/Term.idr)

```idris
public export
data Term : Scoped where
     -- ... existing constructors ...
     
     -- Clock variable reference
     TClock : FC -> (name : Name) -> Term vars
     
     -- Later modality: ▶κ A
     TLater : FC -> (clock : Term vars) -> (ty : Term vars) -> Term vars
     
     -- next κ a : introduce guarded value
     TNext : FC -> (clock : Term vars) -> (arg : Term vars) -> Term vars
     
     -- Tick abstraction: λ̲κ. t
     TTickAbs : FC -> (clock : Name) -> (body : Term (Scope.bind vars clock)) -> Term vars
     
     -- Tick application: t @κ
     TTickApp : FC -> (fn : Term vars) -> (clock : Term vars) -> Term vars
     
     -- Guarded fixpoint
     TFix : FC -> (clock : Term vars) -> (body : Term vars) -> Term vars
```

### 4.2 New Binder Type

```idris
public export
data Binder type
     -- ... existing binders ...
     ClockBind : FC -> Binder type  -- (κ : Clock) binding
```

### 4.3 New LazyReason

```idris
public export
data LazyReason 
     = LInf 
     | LLazy 
     | LUnknown
     | LLater (Term vars)  -- NEW: guarded by specific clock
```

---

## 5. Surface AST Extensions (TTImp/TTImp.idr)

```idris
public export
data RawImp' nm
     -- ... existing constructors ...
     
     -- Clock type
     IClockType : FC -> RawImp' nm
     
     -- Later type: Later κ A
     ILater : FC -> (clock : RawImp' nm) -> (ty : RawImp' nm) -> RawImp' nm
     
     -- next κ e
     INext : FC -> (clock : RawImp' nm) -> (arg : RawImp' nm) -> RawImp' nm
     
     -- Tick abstraction: \tick κ => e
     ITickAbs : FC -> (clock : nm) -> (body : RawImp' nm) -> RawImp' nm
     
     -- Tick application: e @tick κ
     ITickApp : FC -> (fn : RawImp' nm) -> (clock : RawImp' nm) -> RawImp' nm
     
     -- Clock Pi: (κ : Clock) -> A
     IClockPi : FC -> (name : nm) -> (retTy : RawImp' nm) -> RawImp' nm
     
     -- Guarded fix
     IFix : FC -> (clock : RawImp' nm) -> (body : RawImp' nm) -> RawImp' nm
```

---

## 6. Example Programs

### 6.1 Basic Streams

```idris
-- Stream type with guarded tail
record Stream (κ : Clock) (A : Type) where
  constructor MkStream
  head : A
  tail : Later κ (Stream κ A)

-- Cons operator
(::) : A -> Later κ (Stream κ A) -> Stream κ A
x :: xs = MkStream x xs

-- Productive definition
ones : (κ : Clock) -> Stream κ Nat
ones κ = 1 :: next κ (ones κ)
```

### 6.2 Stream Operations

```idris
-- Map over streams (compositional!)
mapS : (a -> b) -> Stream κ a -> Stream κ b
mapS f s = MkStream (f s.head) (next κ (mapS f (s.tail @κ)))

-- Zip two streams
zipWithS : (a -> b -> c) -> Stream κ a -> Stream κ b -> Stream κ c
zipWithS f s1 s2 = 
  MkStream (f s1.head s2.head) 
           (next κ (zipWithS f (s1.tail @κ) (s2.tail @κ)))

-- Fibonacci stream
fibs : (κ : Clock) -> Stream κ Nat
fibs κ = 0 :: next κ (fibs' κ)
  where
    fibs' : (κ : Clock) -> Stream κ Nat
    fibs' κ = 1 :: next κ (zipWithS (+) (fibs κ) (fibs' κ))
```

### 6.3 Generic Guarded Fixpoint

```idris
-- Using fix explicitly
fixExample : (κ : Clock) -> Stream κ Nat
fixExample κ = fix κ (\later => 
  0 :: next κ (mapS S (later @κ)))
```

### 6.4 Removing Clock Quantification

```idris
-- Turn a clocked stream into a regular coinductive stream
delay : ((κ : Clock) -> Stream κ A) -> Inf (Stream A)
delay s = Delay (s _)

-- The magic underscore infers a fresh clock
```

---

## 7. Elaboration Rules

### 7.1 next elaboration

```
Γ ⊢_elab e : A       Γ ⊢_elab κ : Clock
----------------------------------------
Γ ⊢_elab next κ e : ▶κ A

Elaborates to: TNext fc (elab κ) (elab e)
```

### 7.2 Tick abstraction elaboration

```
Γ, κ : Clock ⊢_elab e : A    κ ∉ fv(A)
---------------------------------------
Γ ⊢_elab \tick κ => e : (κ : Clock) -> A

Elaborates to: TTickAbs fc κ (elab e)
```

### 7.3 Tick application elaboration

```
Γ ⊢_elab f : (κ : Clock) -> A    Γ ⊢_elab κ : Clock
---------------------------------------------------
Γ ⊢_elab f @tick κ : A[κ/κ']

Elaborates to: TTickApp fc (elab f) (elab κ)
```

### 7.4 Clock irrelevance check

After elaboration, verify that the result type doesn't mention the clock:

```idris
checkClockIrrelevant : Term vars -> Name -> Core ()
checkClockIrrelevant ty clock = 
  if clock `elem` freeVars ty
  then throw (ClockNotIrrelevant fc clock ty)
  else pure ()
```

---

## 8. Productivity Checker Integration

### 8.1 Extension to Guardedness State

Current (Row 36):
```idris
data Guardedness = Toplevel | Unguarded | Guarded | InDelay
```

Extended for Row 41:
```idris
data Guardedness 
     = Toplevel 
     | Unguarded 
     | Guarded 
     | InDelay 
     | InLater (Term vars)  -- NEW: guarded by specific clock term
```

### 8.2 Recognizing Productive Calls

In `Core/Termination/CallGraph.idr`:

```idris
-- If we're under a next κ, mark subsequent calls as InLater κ
findSC defs env (InLater clock) pats (TNext _ c tm)
    = if clocksMatch clock c
       then findSC defs env (InLater clock) pats tm
       else findSC defs env Unguarded pats tm

-- Recursive calls in InLater state are productive
findSCcall defs env (InLater clock) pats fc fn args
    = if fn == self
       then pure []  -- Productive call, don't record as SCCall
       else -- Check arguments normally
```

### 8.3 Clock Matching

```idris
clocksMatch : Term vars -> Term vars -> Bool
clocksMatch (TClock _ n1) (TClock _ n2) = n1 == n2
clocksMatch _ _ = False
```

---

## 9. Backend Compilation

### 9.1 Runtime Representation

Clocks are purely compile-time entities. At runtime:

| Source | Runtime |
|--------|---------|
| `▶κ A` | Thunk (like `Inf A`) |
| `next κ a` | Delay thunk |
| `t @κ` | Force thunk |
| `λ̲κ. t` | Lambda (no argument) |
| Clocks | Erased |

### 9.2 Optimizations

After productivity checking, clock operations can be erased:

```idris
-- Before erasure
f : (κ : Clock) -> ▶κ Nat -> Nat
f κ x = x @κ + 1

-- After erasure
f : Thunk Nat -> Nat
f x = force x + 1
```

---

## 10. TTC Serialization

New tags for `Core/TTC.idr`:

```idris
-- Term tags
TagTLater : Int
TagTNext : Int
TagTTickAbs : Int
TagTTickApp : Int
TagTFix : Int
TagTClock : Int

-- LazyReason tag
TagLLater : Int
```

---

## 11. Error Messages

### 11.1 Clock Escape

```
Error: Clock variable κ escapes its scope in the result type

  Expected: (κ : Clock) -> Stream κ Nat -> Nat
  Found:    (κ : Clock) -> Stream κ Nat -> ▶κ Nat
                              ^^
  The clock κ appears in the result type, but clock-quantified
  functions must return clock-irrelevant types.
  
  Hint: Use fix κ to eliminate the later modality.
```

### 11.2 Unguarded Recursion

```
Error: Unguarded recursive call in guarded definition

  ones κ = 1 :: ones κ
              ^^^^^^^^^^
  
  Recursive calls in guarded definitions must be wrapped in 'next'.
  
  Suggested fix:
    ones κ = 1 :: next κ (ones κ)
```

---

## 12. Implementation Phases

### Phase 1: Core Type Theory
- [ ] Add clock constructors to `Core/TT/Term.idr`
- [ ] Add `LLater` to `LazyReason`
- [ ] Update TTC serialization
- [ ] Add primitive `Clock` type to context

### Phase 2: Surface Syntax
- [ ] Extend `TTImp/TTImp.idr` with clock AST nodes
- [ ] Add parser support for clock syntax
- [ ] Add desugaring rules

### Phase 3: Elaboration
- [ ] Elaborate clock types
- [ ] Elaborate tick abstraction/application
- [ ] Clock irrelevance checking
- [ ] `next` and `fix` elaboration

### Phase 4: Productivity
- [ ] Extend `Guardedness` with `InLater`
- [ ] Update `findSC` to recognize clock-guarded calls
- [ ] Test with examples

### Phase 5: Library
- [ ] Define `Stream` type using guarded recursion
- [ ] Port existing coinductive examples
- [ ] Documentation

---

## 13. References

1. Atkey & McBride (2013). "Productive Coprogramming with Guarded Recursion"
2. Bahr et al. (2017). "The Clocks Are Ticking: No More Delays!"
3. Agda Documentation: "Guarded Cubical Type Theory" (--guarded flag)
4. Idris 2 FEATURES.md: Rows 36, 38, 41

---

## 14. Open Questions

1. **Syntax**: Should we use Unicode `▶` or ASCII `Later`?
2. **Inference**: Can we infer clock arguments like `next (ones _)`?
3. **Cubical**: How does this interact with future cubical features?
4. **Backend**: Should we optimize away all clocks, or keep some for debugging?
