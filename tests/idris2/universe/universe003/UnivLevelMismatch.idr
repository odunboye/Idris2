module UnivLevelMismatch

-- This should succeed: Type 0 : Type 1 (stratification)
ok1 : Type 1
ok1 = Type 0

-- This should succeed: Type 1 : Type 2
ok2 : Type 2
ok2 = Type 1

-- This should fail: Type 1 has type Type 2, not Type 0
failing1 : Type 0
failing1 = Type 1
