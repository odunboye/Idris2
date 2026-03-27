# Pattern Synonyms Example

This example demonstrates Idris 2's pattern synonym functionality, which allows
defining aliases for patterns.

## Overview

Pattern synonyms let you define names for commonly used patterns, making code
more readable and maintainable. They are especially useful for:

- Hiding implementation details of data types
- Providing semantic names for numeric or string constants
- Simplifying complex nested patterns

## Syntax

```idris
-- Simple pattern synonym (no arguments)
pattern PatternName = constructor

-- Pattern synonym with arguments
pattern PatternName arg1 arg2 = Constructor arg1 arg2
```

## Files

- **Main.idr** - Demonstrates various uses of pattern synonyms

## Features Demonstrated

### 1. Simple Pattern Synonyms

Pattern synonyms without arguments work like constants:

```idris
pattern OK = 200
pattern NotFound = 404
```

### 2. Pattern Synonyms with Arguments

Pattern synonyms can take parameters:

```idris
pattern Single x = [x]
pattern Pair a b = (a, b)
pattern MyCons x xs = (::) x xs
```

### 3. Using Pattern Synonyms

Pattern synonyms can be used in function definitions and case expressions:

```idris
isSuccess : Int -> Bool
isSuccess OK = True
isSuccess _ = False

describe : Int -> String
describe code = case code of
  OK => "Success"
  NotFound => "Not found"
  _ => "Unknown"
```

## Known Limitations

- Pattern synonym names that conflict with existing constructor names (like `Cons`
  or `Nil` for lists) may cause issues. Use different names like `MyCons` and `MyNil`.
- Bidirectional pattern synonyms (usable in expressions) are parsed but not fully
  implemented.

## Building and Running

```bash
idris2 --build pattern-synonyms.ipkg
./build/exec/pattern-synonyms-example
```

Expected output:
```text
Pattern Synonym Examples
========================
isSuccess 200: True
isSuccess 404: False
describe 200: Success
describe 500: Server error
getFirst [1,2,3]: 1
getFirst []: 0
getFirstPair (10,20): 10
```

## Benefits

- **Abstraction**: Hide internal representation details
- **Readability**: Use domain-specific names instead of implementation details
- **Refactoring**: Change implementation without breaking client code
- **Zero runtime cost**: Pattern synonyms are expanded at compile time
