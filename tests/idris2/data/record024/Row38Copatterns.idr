-- Row 38: Copattern matching — define record values by specifying each field.
-- A copattern definition  f .field = rhs  desugars to
--   f = MkRecord ... rhs ...
-- using the constructor of f's declared record return type.

%default total

-- 1. Simple record with two fields
record Pair' a b where
  constructor MkPair'
  fst' : a
  snd' : b

myPair : Pair' Nat Nat
myPair .fst' = 1
myPair .snd' = 2

-- 2. Coinductive stream defined by copatterns
record CoStream a where
  constructor MkCoStream
  hd : a
  tl : Inf (CoStream a)

ones : CoStream Nat
ones .hd = 1
ones .tl = ones

nats : Nat -> CoStream Nat
nats n = MkCoStream n (nats (S n))

-- 3. Helper: take elements from a CoStream
takeCS : Nat -> CoStream a -> List a
takeCS Z _     = []
takeCS (S n) s = s.hd :: takeCS n (Force s.tl)

-- 4. Record with three fields
record Triple a b c where
  constructor MkTriple
  fst3 : a
  snd3 : b
  thd3 : c

myTriple : Triple Nat String Bool
myTriple .fst3 = 42
myTriple .snd3 = "hello"
myTriple .thd3 = True

main : IO ()
main = do
  -- Pair copatterns
  printLn (fst' myPair)
  printLn (snd' myPair)
  -- Coinductive stream
  printLn (takeCS 5 ones)
  printLn (takeCS 5 (nats 0))
  -- Triple copatterns
  printLn (fst3 myTriple)
  printLn (snd3 myTriple)
  printLn (thd3 myTriple)
