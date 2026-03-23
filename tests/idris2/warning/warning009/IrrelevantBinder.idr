module IrrelevantBinder

-- Basic irrelevant Pi: .(x : A) -> B
-- The argument is erased at runtime (like Rig0) and logically irrelevant.

-- Identity-like function that takes an irrelevant Nat
irrelId : .(x : Nat) -> Nat
irrelId _ = 0

-- Const function with an irrelevant first argument
irrelConst : .(x : Nat) -> Nat -> Nat
irrelConst _ n = n
