# Feature: Termination / Positivity Pragmas (Row 22)

## Purpose

This feature provides **controlled escape hatches** when Idris' conservative checks reject valid code. These pragmas allow programmers to bypass specific totality checks when they know the code is sound, while making such bypasses visible and auditable.

## The Three Pragmas

### 1. `%no_positivity_check` on data declarations

**Problem**: The strict positivity checker rejects some data types that are actually sound. For example, types with higher-order constructors or certain recursive patterns.

**Purpose**: Allow defining these data types when you know they're sound, while explicitly marking that you've bypassed the check.

**Example**:
```idris
%no_positivity_check
data Weird : Type where
  MkWeird : ((Weird -> Bool) -> Bool) -> Weird
```

### 2. `%terminating` declaration pragma

**Problem**: Currently you use `assert_total` buried in the function body to mark a definition as terminating. This is invisible to code review and looks hacky.

**Purpose**: Make escape hatches **visible at the declaration level**, similar to how `partial`/`covering` work:

**Example**:
```idris
%terminating
ackermann : Nat -> Nat -> Nat
ackermann Z n = S n
ackermann (S m) Z = ackermann m (S Z)
ackermann (S m) (S n) = ackermann m (ackermann (S m) n)
```

This is more auditable than `assert_total` buried in the body.

### 3. `%no_coverage_check`

**Problem**: `partial` currently conflates "non-terminating" with "non-exhaustive pattern matching." You can't express "this terminates but has incomplete patterns by design."

**Purpose**: Decouple coverage from totality, allowing intentional partial pattern matching when appropriate.

**Example**:
```idris
%no_coverage_check
fromJust : Maybe a -> a
fromJust (Just x) = x
-- No Nil case - we know it's never called with Nothing
```

## Why This Matters

- **Library evolution**: Some valid data type designs are rejected by the strict positivity checker
- **Code review**: Declaration-level pragmas are visible; `assert_total` hidden in bodies is not
- **Well-founded recursion**: Remove need for `assert_total` on structurally-clear but non-structural recursion
- **Safety**: All these pragmas are banned by `--safe` mode, so they don't compromise verified code

## Implementation Notes

- `%no_positivity_check` is stored as a `DataOpt` in the `TCon` definition
- `%terminating` is stored as a `TotalReq` flag (new constructor `Unchecked`)
- `%no_coverage_check` is stored as a `DefFlag`
- All three pragmas are banned when `--safe` mode is enabled
