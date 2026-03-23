module IrrelevantEnforce

-- Attempting to use an irrelevant argument in a relevant (value) position
-- must be rejected with "not accessible in this context"
bad : .(x : Nat) -> Nat
bad x = x
