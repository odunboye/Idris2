-- Test file for pattern synonyms (Row 12)
-- Exercises parsing, LHS expansion, and RHS expansion.

module PatternSynonyms

import Builtin
import Data.Bool
import Data.Nat
import Data.List

%default total

-- Zero-argument synonym (alias for a constructor)
pattern Zero = Z

-- One-argument synonym
pattern Succ n = S n

-- Two-argument synonym
pattern Cons h t = h :: t

-- Zero-argument synonym returning a pair
pattern MyPair a b = MkPair a b

-- Use in function signatures and LHS patterns
isZero : Nat -> Bool
isZero Zero = True
isZero (Succ _) = False

-- Synonym used in both LHS (deconstruct) and RHS (construct)
pred : Nat -> Nat
pred Zero = Zero
pred (Succ n) = n

-- Two-arg synonym on LHS
isCons : List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

-- Two-arg synonym on RHS
prependOne : List Nat -> List Nat
prependOne xs = Cons 1 xs

-- Pair synonym on LHS and RHS
swap : (a, b) -> (b, a)
swap (MyPair x y) = MyPair y x
