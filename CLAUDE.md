# Idris2 Dependent Type Rewrite Implementation

This document describes the dependent type rewrite implementation in this fork of Idris2.

## Overview

Upstream Idris2 documented a gap:
> `rewrite` doesn't yet work on dependent types

This implementation closes that gap with two key fixes:

1. **Auto-sym** - Automatically applies `sym` when the goal contains the RHS of the equality
2. **replaceWithUnify** - Uses unification to solve metas in argument-position rewrites

## Changes Made

### Core Implementation

#### 1. Auto-sym (`src/TTImp/Elab/Rewrite.idr`)

When `prf : lt = rt` and the goal contains `rt` (not `lt`), `rewrite prf` now automatically uses `sym prf`.

**Before:**
```idris
stripZero : (prf : n + 0 = n) -> Vect (n + 0) a -> Vect n a
stripZero prf xs = rewrite sym prf in xs  -- Had to write sym explicitly
```

**After:**
```idris
stripZero : (prf : n + 0 = n) -> Vect (n + 0) a -> Vect n a
stripZero prf xs = rewrite prf in xs  -- Auto-sym fires automatically
```

**Implementation details:**
- On the delayed elaboration retry (`delayed = True`), if forward search finds nothing, `elabRewrite` also searches for the RHS in the goal
- If found, wraps the proof in `sym` before building `rewrite__impl`
- Strategy 2 (delayed pass) handles this case

#### 2. replaceWithUnify (`src/Core/AutoSearch.idr`)

When `rewrite prf in xs` appears in function-argument position where the expected type contains an unsolved meta (e.g., `Vect (S ?k) a`), the old `replace'` couldn't match through the meta.

The new `replaceWithUnify` falls back to `unify`, which can solve the meta as a side effect.

**Example:**
```idris
myHead : {n : Nat} -> Vect (S n) a -> a
myHead (x :: _) = x

withMeta : (prf : n = S m) -> Vect n a -> a
withMeta prf xs = myHead (rewrite prf in xs)  -- ?k unified to m
```

**Implementation details:**
- When `replace'` (pure `convert`-based substitution) finds nothing
- `replaceWithUnify` tries `unify inTerm` against each sub-NF
- This can solve metas as a side effect

### Use Cases

The `use-cases/dependent-rewrite/` directory contains 8 modules demonstrating the fixes:

| Module | Demonstrates |
|--------|--------------|
| `RewriteBasics.idr` | Core `rewrite` mechanism, forward rewrite |
| `AutoSym.idr` | Auto-sym when goal contains RHS |
| `IndexRewriting.idr` | Rewriting type indices of Vect, Fin, Matrix |
| `ArgumentRewriting.idr` | `rewrite … in expr` in function-argument position |
| `InductiveProofs.idr` | Nat arithmetic, List lemmas, multi-rewrite chains |
| `VectProofs.idr` | Full Vect library: reverse, interleave, map fusion |
| `AdvancedChains.idr` | Multi-rewrite chains, RingBuf, merge sort |
| `Main.idr` | Entry point demonstrating all features |

**Build use-cases:**
```bash
cd use-cases/dependent-rewrite
idris2 --build dependent-rewrite.ipkg
./build/exec/dependent-rewrite
```

## Test Results

### Compiler Test Suite
- All 681 tests pass ✓
- New test: `tests/idris2/deprewrite/deprewrite001/` for dependent rewrite

### Use-Cases
All 8 modules type-check and build successfully:
```
1/8: Building InductiveProofs
2/8: Building ArgumentRewriting
3/8: Building IndexRewriting
4/8: Building AutoSym
5/8: Building RewriteBasics
6/8: Building AdvancedChains
7/8: Building VectProofs
8/8: Building Main
```

## Git History

Key commits in `fix-dep-rewrite` branch:

```
a43978e fix: resolve all 3 spurious test failures
5e699072 feat: replaceWithUnify — close the remaining dependent-rewrite gap
06b953e7 fix: goalHasDelayed — block auto-sym only on Delayed holes, not regular metas
314f20ea feat: dependent rewrite — auto-sym (sub-problem A) + het infrastructure (sub-problem B partial)
```

## Installation

The compiler is installed at `~/.idris2/bin/idris2`:

```bash
$ idris2 --version
Idris 2, version 0.8.0-a43978e38
```

## Known Issues

### LSP Status
The idris2-lsp server has version mismatches between LSP-lib source and installed version. This causes initialization failures.

**Workaround:** Use command-line compiler:
```bash
idris2 --check YourFile.idr
idris2 --build your-package.ipkg
```

**Impact:** The dependent rewrite implementation itself is fully functional. LSP fix is cosmetic.

## Key Patterns

| Pattern | Mechanism | Example |
|---------|-----------|---------|
| `rewrite prf in xs` forward | strategy 1 — `replace'` + `convert` | `coerce : m=n → Vect m a → Vect n a` |
| `rewrite prf in xs` when goal has RHS | strategy 2 — auto-sym + `replace'` | `stripZero : Vect (n+0) a → Vect n a` |
| `rewrite prf in f xs` argument position | strategy 2 + `replaceWithUnify` | `myHead (rewrite prf in xs)` |
| Sequential rewrites | strategies 1/2 per step | `multDistribLeft` (6 rewrites) |

## References

- Original gap documented in upstream Idris2
- Implementation: `src/TTImp/Elab/Rewrite.idr` (auto-sym)
- Implementation: `src/Core/AutoSearch.idr` (replaceWithUnify)
- Use-cases: `use-cases/dependent-rewrite/`

## Verification

To verify the implementation:

```bash
# 1. Check compiler version
idris2 --version  # Should show 0.8.0-a43978e38

# 2. Build use-cases
cd use-cases/dependent-rewrite
idris2 --build dependent-rewrite.ipkg

# 3. Run executable
./build/exec/dependent-rewrite

# 4. Check specific file
idris2 --check src/AutoSym.idr
```

All should complete without errors.
