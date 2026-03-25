||| Row 28 — Definitional η-equality for records
|||
||| Two values of the same record type are definitionally equal if and only if
||| all their fields are definitionally equal.  Concretely:
|||
|||   r ≡ MkR (r.f1) (r.f2) ...       (η-expansion)
|||
||| This is checked by applying each field projector to the neutral term and
||| comparing field-by-field in Core.Normalise.Convert.
module EtaRecord

------------------------------------------------------------------------
-- 1. Simple pair record

record Pair' a b where
  constructor MkPair'
  fst' : a
  snd' : b

-- η: the eta-expansion of a neutral record equals the record itself.
etaExpand : (r : Pair' a b) -> MkPair' (fst' r) (snd' r) = r
etaExpand r = Refl

-- swap ∘ swap = id  (uses η to finish the proof)
swap' : Pair' a b -> Pair' b a
swap' p = MkPair' (snd' p) (fst' p)

swapSwapId : (p : Pair' a b) -> swap' (swap' p) = p
swapSwapId p = Refl

------------------------------------------------------------------------
-- 2. Unit record (zero fields)

record Unit' where
  constructor MkUnit'

unitEta : (u : Unit') -> MkUnit' = u
unitEta u = Refl

------------------------------------------------------------------------
-- 3. Single-field record (newtype-like)

record Wrap a where
  constructor MkWrap
  unwrap : a

wrapEta : (w : Wrap a) -> MkWrap (unwrap w) = w
wrapEta w = Refl

------------------------------------------------------------------------
-- 4. Dependent record (Sigma type)

record Sigma' (a : Type) (b : a -> Type) where
  constructor MkSigma'
  dfst : a
  dsnd : b dfst

sigmaEta : (s : Sigma' a b) -> MkSigma' (dfst s) (dsnd s) = s
sigmaEta s = Refl

------------------------------------------------------------------------
-- 5. Concrete computation via η

addPairs : Pair' Nat Nat -> Pair' Nat Nat -> Pair' Nat Nat
addPairs p q = MkPair' (fst' p + fst' q) (snd' p + snd' q)

-- addPairs with zero on left: (0,0) + p = p (0+n=n definitionally, then eta)
addZeroLeftId : (p : Pair' Nat Nat) -> addPairs (MkPair' 0 0) p = p
addZeroLeftId p = Refl

main : IO ()
main = do
  putStrLn "Row 28: η-equality for records"
  putStrLn ""
  putStrLn "  etaExpand     : MkPair' (fst' r) (snd' r) = r       OK"
  putStrLn "  swapSwapId    : swap' (swap' p) = p                 OK"
  putStrLn "  unitEta       : MkUnit' = u                         OK"
  putStrLn "  wrapEta       : MkWrap (unwrap w) = w               OK"
  putStrLn "  sigmaEta      : MkSigma' (dfst s) (dsnd s) = s      OK"
  putStrLn "  addZeroLeftId : addPairs (0,0) p = p                OK"
  putStrLn ""
  putStrLn "  All Refl proofs passed — η-equality is definitional."
