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

---

## Feature: Opaque Definitions (Row 29)

### Overview

`%opaque` controls **when the type checker is allowed to unfold a definition** — it separates "this value exists and can be computed" from "the type checker may substitute its body".

### The Core Problem It Solves

By default, Idris2's normaliser eagerly unfolds every definition. That means if you write:

```idris
cacheSize : Nat
cacheSize = 1024
```

The type checker treats `cacheSize` and `1024` as definitionally equal everywhere. That's usually fine, but it creates two problems:

1. **Abstraction leaks.** A library author who exposes `cacheSize` doesn't want callers writing proofs that depend on the fact that it equals `1024` — that's an internal detail that could change.

2. **Performance / error message pollution.** A large or recursive definition gets unfolded in every error message and every constraint, making them unreadable.

### The Two Pragmas

#### `%opaque name`

```idris
%opaque cacheSize
```

After this, the normaliser treats `cacheSize` as a *stuck neutral term* — it won't look inside it. The value is still there at runtime, and you can still call functions that take a `Nat`. But:

```idris
bad : cacheSize = 1024
bad = Refl  -- ERROR: cacheSize is irreducible
```

#### `%reducible name`

An escape hatch — restores unfolding for a specific definition. Useful for writing an internal proof, then sealing again:

```idris
%reducible cacheSize
proof : cacheSize = 1024
proof = Refl       -- OK
%opaque cacheSize  -- sealed again
```

### Why Opaque Definitions Matter

- **Abstraction without module boundaries**: Per-definition, reversible opacity within a single file — finer-grained than a module boundary.
- **Library evolution**: Internal implementation constants can be changed without breaking downstream proofs.
- **Error message clarity**: Opaque definitions stay symbolic in error messages instead of being unfolded into large expressions.
- **Explicit abstraction boundary**: Makes it clear to readers which values are "part of the public contract" vs "implementation details."

### Analogy to Other Languages

| Concept | Language |
|---|---|
| `private` / module boundary | ML, Haskell |
| `opaque` type alias (`.mli` files) | OCaml |
| `@[irreducible]` attribute | Lean 4 |

Idris2's version is finer-grained than a module boundary: it is **per-definition** and **reversible within the same file**.

### Implementation Details

- New `Reducibility` type (`Reducible | SemireducibleInst | Irreducible`) stored as a field on `GlobalDef` in `Core.Context`
- `evalRef` in `Core.Normalise.Eval` short-circuits when `reducibility == Irreducible`
- `SemireducibleInst` (reserved for interface instances) is blocked in normal unification but allowed when `EvalOpts.inSearch = True` (interface resolution mode)
- `%opaque` / `%reducible` are standalone directives (like `%hide`) parsed in `Idris.Parser`, desugared in `Idris.Desugar` via `IPragma`
- Serialised to TTC so opacity survives incremental compilation
