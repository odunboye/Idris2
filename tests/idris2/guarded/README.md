# Row 41: Guarded Recursion / Clock Variables

This directory contains tests for the guarded recursion implementation based on Atkey & McBride (2013).

## What is Guarded Recursion?

Guarded recursion is a type-based approach to ensuring productivity of corecursive definitions. It uses:

- **Clocks**: Abstract notions of time/ticks (`Clock` / `%Clock`)
- **Later modality**: `Later κ A` means "A is available after one tick on clock κ"
- **Tick abstraction**: `\tick κ => e` binds a tick on clock κ
- **Fixpoint combinator**: `fix κ f` for productive recursion

## The Data.Guarded Library

Located in `libs/base/Data/Guarded.idr`, this module provides:

### Core Types
- `Clock` - The clock primitive
- `Later k a` - The later modality ▶k A
- `Tick k` - Ticks for forcing guarded values

### Constructors/Eliminators
- `next : (k : Clock) -> a -> Later k a` - Introduce guarded value
- `force : Later k a -> a` - Eliminate guarded value
- `fix : (k : Clock) -> (Later k a -> a) -> a` - Guarded fixpoint

### Type Class Instances
- `Functor (Later k)` - `map` for guarded values
- `Applicative (Later k)` - `pure`, `<*>`, `liftA2`, `liftA3`
- `Monad (Later k)` - `>>=`, `join`

### Utility Functions
- `sequence : List (Later k a) -> Later k (List a)` - Sequence guarded list
- `traverse : (a -> Later k b) -> List a -> Later k (List b)` - Map and sequence
- `zip / zip3` - Zip guarded values together
- `andLater / orLater / notLater / ifLater` - Boolean operations
- `liftOp / liftOp1` - Lift operators to guarded values
- `delayN : Nat -> a -> Later k a` - Delay for N ticks
- `foldrLater` - Fold with guarded combining function

### Tick Utilities
- `withTick : (Tick k -> a) -> Later k a` - Create guarded with tick
- `andThen : Later k a -> (a -> Tick k -> b) -> Later k b` - Sequence with tick

## Tests

### guarded001 - Comprehensive Library Tests
Tests all features of the `Data.Guarded` library:
- Clock type and ticks
- Later modality with `next`/`force`
- Functor instance (map)
- Applicative instance (pure, <*>, liftA2)
- Monad instance (>>=)
- Boolean operations
- Utility functions (zip, liftOp, delayN)
- `fix` combinator

### guarded002 - Extended Features
Additional tests for edge cases and implicit arguments.

## Usage Examples

### Basic Guarded Values
```idris
import Data.Guarded

%default total

-- Delay a value by one tick
answer : (k : Clock) -> Later k Nat
answer k = next k 42

-- Map over guarded values
double : (k : Clock) -> Later k Nat -> Later k Nat
double k = map (2 *)

-- Combine guarded values
addGuarded : (k : Clock) -> Later k Nat -> Later k Nat -> Later k Nat
addGuarded k la lb = liftA2 (+) la lb
```

### Productive Recursion with fix
```idris
-- Infinite stream of ones (conceptually)
ones : (k : Clock) -> Later k Nat
ones k = fix k (\rec => next k 1)

-- Counting up (conceptually)
countFrom : (k : Clock) -> Nat -> Later k Nat
countFrom k n = fix k (\rec => next k n)
```

### Monadic Style
```idris
-- Chain guarded computations
incrementLater : (k : Clock) -> Later k Nat -> Later k Nat
incrementLater k la = do
  n <- la
  pure (n + 1)

-- Using applicative style
triple : (k : Clock) -> Later k Nat -> Later k Nat
triple k la = pure (3 *) <*> la
```

### Boolean Operations
```idris
-- Guarded boolean logic
guardedAnd : (k : Clock) -> Later k Bool -> Later k Bool -> Later k Bool
guardedAnd k = andLater

guardedIf : (k : Clock) -> Later k Bool -> Later k a -> Later k a -> Later k a
guardedIf k = ifLater
```

## Implementation Status

| Feature | Status | Notes |
|---------|--------|-------|
| Clock primitive (`%Clock`) | ✅ | Working |
| Later type (`Later κ A`) | ✅ | Working with Functor/Applicative/Monad |
| `next` constructor | ✅ | Working |
| `force` eliminator | ✅ | Working |
| Tick abstraction (`\tick κ => e`) | ✅ | Working |
| `fix` combinator | ✅ | Working (with `assert_total`) |
| Functor instance | ✅ | `map` |
| Applicative instance | ✅ | `pure`, `<*>`, `liftA2`, `liftA3` |
| Monad instance | ✅ | `>>=`, `join` |
| Boolean operations | ✅ | `andLater`, `orLater`, `notLater`, `ifLater` |
| Utility functions | ✅ | `zip`, `sequence`, `traverse`, `delayN`, etc. |
| Productivity checker | ✅ | Basic implementation |

## Known Limitations

1. **Syntactic clock matching**: The productivity checker uses simple equality. Complex clock passing may not be tracked.

2. **No built-in Stream type**: Would require positivity workarounds.

3. **`fix` uses `assert_total`**: This is a pragmatic choice. The safety is enforced by the productivity checker on uses of `fix`.

4. **Clocks not erased at runtime**: Have runtime representation currently.

## References

- Atkey & McBride (2013): "Productive Coprogramming with Guarded Recursion"
