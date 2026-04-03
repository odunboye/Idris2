module SafeCLI

-- assert_total should be banned when --safe is passed
bad : Nat -> Nat
bad n = assert_total (n + 1)
