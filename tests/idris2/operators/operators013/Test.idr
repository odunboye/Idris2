module Test

-- Row 14: Unicode Mathematical Operators as operator characters.
-- Characters in U+2200–U+22FF and U+2A00–U+2AFF are now valid operator chars.

-- Logical conjunction and disjunction
export infixr 5 ∧
export infixr 4 ∨

export
(∧) : Bool -> Bool -> Bool
True  ∧ y = y
False ∧ _ = False

export
(∨) : Bool -> Bool -> Bool
True  ∨ _ = True
False ∨ y = y

-- Membership
export infix 6 ∈

export
(∈) : Eq a => a -> List a -> Bool
(∈) = elem

-- Subscript-digit variable names (x₁, xₙ) — already worked, verified here.
export
swap₂ : (a, b) -> (b, a)
swap₂ (x₁, x₂) = (x₂, x₁)

-- Proofs
prop1 : True ∧ True = True
prop1 = Refl

prop2 : False ∧ True = False
prop2 = Refl

prop3 : (3 ∈ [1,2,3]) = True
prop3 = Refl
