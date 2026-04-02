module ProofIrrel

import Data.Squash

-- Row 42: Definitional proof irrelevance for squash-like types.
--
-- MkSquash : .(x : a) -> Squash a
-- The argument is erased (rig 0), so the converter and unifier treat
-- any two values of the same squash type as definitionally equal.

-- 1. Concrete values: MkSquash 42 = MkSquash 99 definitionally
squashConcreteEq : MkSquash 42 = MkSquash 99
squashConcreteEq = Refl

-- 2. Abstract values: p = q for any p q : Squash a
irrelRefl : (p : Squash a) -> (q : Squash a) -> p = q
irrelRefl p q = Refl

-- 3. Works via the squash constructor
squashEq : (x : Nat) -> (y : Nat) -> squash x = squash y
squashEq x y = Refl

-- 4. Works for Squash of a function type
funSquash : (f : Squash (Nat -> Nat)) -> (g : Squash (Nat -> Nat)) -> f = g
funSquash f g = Refl

main : IO ()
main = do
  putStrLn "=== Row 42: Definitional Proof Irrelevance ==="
  putStrLn ""
  putStrLn "squashConcreteEq = Refl  -- MkSquash 42 = MkSquash 99"
  putStrLn "irrelRefl p q = Refl    -- any p q : Squash a are definitionally equal"
  putStrLn "squashEq x y = Refl    -- squash x = squash y"
  putStrLn "funSquash f g = Refl   -- works for Squash of any type"
  putStrLn ""
  putStrLn "OK"
