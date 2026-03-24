module IrrelevantLambda

-- Irrelevant Pi binder: .(x : A) -> B
-- The argument is erased and logically irrelevant.

-- Top-level form: pattern binder on LHS (standard usage)
ignoreLam : .(x : Nat) -> Nat
ignoreLam x = 0

-- Higher-order: irrelevant lambda \.(x : A) => body used as an argument
applyIrrel : (.(x : Nat) -> Nat) -> Nat
applyIrrel f = f 42

result : Nat
result = applyIrrel (\.(x : Nat) => 99)
