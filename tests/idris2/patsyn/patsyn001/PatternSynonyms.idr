-- Test file for pattern synonyms (Row 12)
-- Basic pattern synonym functionality

module PatternSynonyms

%default total

-- Simple pattern synonym (no arguments)
pattern Unit = MkUnit

-- Pattern synonym with arguments  
pattern Cons x xs = x :: xs

-- Pattern synonym for pairs
pattern MkPair a b = (a, b)

-- Test functions using pattern synonyms
isUnit : Unit -> Bool
isUnit Unit = True

isCons : List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

head : List a -> Maybe a
head (Cons x _) = Just x
head _ = Nothing

fst : (a, b) -> a
fst (MkPair x _) = x

snd : (a, b) -> b
snd (MkPair _ y) = y

-- Pattern synonyms can be used in case expressions
testCase : List Nat -> Nat
testCase xs = case xs of
  Cons n _ => n
  _ => 0
