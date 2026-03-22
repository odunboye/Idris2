module UnivHierarchy

-- Tests for universe hierarchy enforcement.
--
-- The rule: Type k : Type (k+1).  Explicit level annotations must respect
-- this — you cannot use Type k where Type j (j <= k) is expected.

-- -----------------------------------------------------------------------
-- Positive cases: things that should type-check
-- -----------------------------------------------------------------------

-- Type 0 lives in Type 1 (the direct case).
good1 : Type 1
good1 = Type 0

-- Type 0 also lives in any higher universe (cumulativity).
good2 : Type 2
good2 = Type 0

-- Type 1 lives in Type 2.
good3 : Type 2
good3 = Type 1

-- A higher level is an upper bound (cumulativity via ascription).
good4 : Type 1
good4 = Type 0

-- -----------------------------------------------------------------------
-- Negative cases: things that must fail
-- -----------------------------------------------------------------------

-- Type 0 : Type 0 — the direct Girard-style paradox (explicit levels).
failing "Universe level error"
  bad1 : Type 0
  bad1 = Type 0

-- Type 1 : Type 0 — a larger universe cannot inhabit a smaller one.
failing "Universe level error"
  bad2 : Type 0
  bad2 = Type 1

-- Type 1 : Type 1 — same level, not strictly smaller.
failing "Universe level error"
  bad3 : Type 1
  bad3 = Type 1
