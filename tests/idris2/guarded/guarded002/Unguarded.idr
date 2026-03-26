-- Test: Basic Clock type recognition with Data.Guarded library
-- This file should compile successfully

import Data.Guarded

%default total

-- Test that Clock primitive type is recognized
clockTest : Clock -> Clock
clockTest k = k

-- Test that Clock can be passed as an implicit argument
clockImplicit : {k : Clock} -> Clock
clockImplicit {k} = k

-- Test tick type
tickTest : (k : Clock) -> Tick k
tickTest k = k

-- Test Later type
laterTest : (k : Clock) -> Later k Nat
laterTest k = next k 42

-- Test fix
constant : (k : Clock) -> Later k Nat
constant k = fix k (\rec => next k 0)
