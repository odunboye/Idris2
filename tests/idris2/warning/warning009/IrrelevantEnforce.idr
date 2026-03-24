module IrrelevantEnforce

-- Attempting to use an irrelevant argument in a relevant (value) position
-- must be rejected with IrrelevantUsed
bad : .(x : Nat) -> Nat
bad x = x
