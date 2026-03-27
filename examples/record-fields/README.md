# Record Fields Example

This example demonstrates the per-record field namespace feature in Idris 2.

## Overview

When multiple records define fields with the same name, you can disambiguate
using the qualified form `RecordName.fieldName`.

## Example

```idris
import Person
import Company

-- Both Person and Company have a 'name' field
-- Use qualified names to disambiguate:
getPersonName : Person -> String
getPersonName = Person.name  -- Refers to Person.name

getCompanyName : Company -> String  
getCompanyName = Company.name  -- Refers to Company.name
```

## Running the Example

```bash
idris2 --build record-fields.ipkg
./build/exec/record-fields-example
```

## Benefits

- No more `personName`/`companyName` workarounds
- Multiple records can share natural field names like `name`, `id`, `status`
- Clear, readable code with explicit disambiguation when needed
