-- Row 36: guardedness / productivity checker for corecursive definitions.
-- Functions whose declared return type is `Inf A` use the productivity
-- checker (Guarded start) instead of the size-change termination checker,
-- producing a "not productive" error rather than "not terminating".

%default total

-- Productive: no recursive call, just wraps a constant.
prodOk : Inf Nat
prodOk = Delay 42

-- Not productive: direct self-reference with no Delay guard.
prodBad : Inf Nat
prodBad = prodBad

-- Stream functions use the existing InDelay path (return type is not Inf).
ones : Stream Nat
ones = 1 :: Delay ones

-- Not productive: recursive call is outside any Delay (inside map).
badOnes : Stream Nat
badOnes = map S badOnes
