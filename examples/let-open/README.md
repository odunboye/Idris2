# Let Open Example

This example demonstrates Idris 2's `let open` syntax for locally opening namespaces.

## Overview

The `let open` syntax allows you to bring all exported names from a namespace into
scope for a single expression. This is similar to Haskell's `let open` or OCaml's
`let open`.

## Syntax

```idris
let open Namespace.Name in expression
```

## Files

- **Main.idr** - Demonstrates various uses of the `let open` syntax

## Features Demonstrated

### 1. Basic Let Open

Open a namespace locally:

```idris
example1 : Int
example1 = let open Data.List in 42
```

### 2. Opening Different Namespaces

You can open any namespace:

```idris
example2 : Int
example2 = let open Data.Nat in 100

example3 : Int
example3 = let open Prelude.List in 200
```

### 3. Nested Let Open

Multiple `let open` can be nested:

```idris
example4 : Int
example4 = 
  let open Data.List in
    let open Data.Nat in
      300
```

### 4. Let Open in Functions

Use `let open` within function definitions:

```idris
example5 : Int -> Int
example5 x = let open Data.List in x + 1
```

## Building and Running

```bash
idris2 --build let-open.ipkg
./build/exec/let-open-example
```

Expected output:
```text
let open syntax examples (parser only)
======================================
These examples demonstrate that the 'let open' syntax parses correctly.
Full semantic support (bringing names into scope) is planned.

example1: 42
example2: 100
example3: 200
example4: 300
example5 5: 6
```

## Current Status

**Parser**: ✅ The `let open` syntax is fully parsed.

**Semantics**: 🚧 The semantic analysis to bring names from the opened namespace
into scope is not yet implemented. The syntax parses correctly but the namespace
contents are not actually made available.

## Future Work

When fully implemented, `let open` will allow:

```idris
-- Instead of writing:
result1 = Data.List.map (* 2) [1, 2, 3]
result2 = Data.List.sum result1

-- You could write:
result = let open Data.List in
  sum (map (* 2) [1, 2, 3])
```

This makes code more concise when using multiple functions from the same module.
