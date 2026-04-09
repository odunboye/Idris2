-- Regression: irrelevant-piinfo variables should be allowed in type positions.
-- Types are erased at runtime, so using an irrelevant-bound variable in a type
-- expression is safe.

data Vec : Nat -> Type -> Type where
  Nil  : Vec 0 a
  (::) : a -> Vec n a -> Vec (S n) a

-- n and m are bound irrelevant (.(x : A) -> syntax).
-- They appear only in type positions: 'n = m', 'Vec n a', 'Vec m a'.
-- Irrelevant args use _ in the LHS pattern; Refl unifies the types.
reindex : .(n : Nat) -> .(m : Nat) -> n = m -> Vec n a -> Vec m a
reindex _ _ Refl xs = xs

-- A simpler case: irrelevant var in return type only.
-- Body ignores n (uses _) since n is not accessible computationally.
identity : .(n : Nat) -> Vec n a -> Vec n a
identity _ xs = xs
