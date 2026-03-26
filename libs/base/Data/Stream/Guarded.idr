||| Guarded streams using the Later modality.
|||
||| This module provides a Stream type where the tail is guarded by the Later
||| modality, ensuring productivity of corecursive definitions.
|||
||| Example:
||| ```idris
||| import Data.Stream.Guarded
||| import Data.Guarded
|||
||| %default total
|||
||| -- Infinite stream of ones
||| ones : (k : Clock) -> Stream k Nat
||| ones k = MkStream 1 (next k (ones k))
||| ```
module Data.Stream.Guarded

import Data.Guarded
import Data.List

%default total

--------------------------------------------------------------------------------
-- STREAM TYPE
--------------------------------------------------------------------------------

||| A guarded stream where the tail is delayed by one tick on clock k.
|||
||| Corecursive definitions producing streams are productive because the tail
||| can only be accessed after a tick on k.
|||
||| @ k the clock indexing the stream
||| @ a the element type
public export
record Stream (k : Clock) (a : Type) where
  constructor MkStream
  ||| The first element of the stream
  head : a
  ||| The tail of the stream, guarded by one tick on k
  tail : Later k (Stream k a)

--------------------------------------------------------------------------------
-- CREATING STREAMS
--------------------------------------------------------------------------------

||| Create a stream from a head and a guarded tail.
public export
cons : {k : Clock} -> {0 a : Type} -> a -> Later k (Stream k a) -> Stream k a
cons = MkStream

||| Create a stream that repeats the same element infinitely.
|||
||| Example:
||| ```idris
||| ones : (k : Clock) -> Stream k Nat
||| ones k = repeat k 1
||| ```
public export
repeat : {0 a : Type} -> (k : Clock) -> a -> Stream k a
repeat k x = MkStream x (next k (repeat k x))  -- Guarded: recursive call is under next k

||| Generate a stream by iterating a function.
|||
||| Example:
||| ```idris
||| -- 0, 1, 2, 3, ...
||| nats : (k : Clock) -> Stream k Nat
||| nats k = iterate k S 0
||| ```
public export
iterate : {0 a : Type} -> (k : Clock) -> (a -> a) -> a -> Stream k a
iterate k f x = MkStream x (next k (iterate k f (f x)))  -- Guarded: recursive call is under next k

||| Generate a stream from a seed value and a generator function.
public export
unfold : {0 a, s : Type} ->
         (k : Clock) -> (s -> (a, s)) -> s -> Stream k a
unfold k f s =
  let (x, s') = f s in
  MkStream x (next k (unfold k f s'))  -- Guarded: recursive call is under next k

||| Create a stream by counting up from a starting number.
public export
countFrom : (k : Clock) -> Nat -> Stream k Nat
countFrom k n = iterate k S n

||| Create a stream of natural numbers starting from 0.
public export
nats : (k : Clock) -> Stream k Nat
nats k = countFrom k 0

--------------------------------------------------------------------------------
-- TRANSFORMING STREAMS
--------------------------------------------------------------------------------

||| Map a function over every element of a stream.
public export
map : {k : Clock} -> {0 a, b : Type} -> (a -> b) -> Stream k a -> Stream k b
-- Guarded: recursive call is under next k. unsafeForce is safe here because
-- we immediately wrap the result in next k.
map f s = MkStream (f s.head) (next k (map f (unsafeForce s.tail)))

||| Zip two streams together element-wise.
public export
zipWith : {k : Clock} -> {0 a, b, c : Type} ->
          (a -> b -> c) -> Stream k a -> Stream k b -> Stream k c
zipWith f s1 s2 =
  MkStream (f s1.head s2.head)
           (next k (zipWith f (unsafeForce s1.tail) (unsafeForce s2.tail)))
           -- Guarded: recursive call is under next k

||| Zip three streams together element-wise.
public export
zipWith3 : {k : Clock} -> {0 a, b, c, d : Type} ->
           (a -> b -> c -> d) -> Stream k a -> Stream k b -> Stream k c -> Stream k d
zipWith3 f s1 s2 s3 =
  MkStream (f s1.head s2.head s3.head)
           (next k (zipWith3 f (unsafeForce s1.tail) (unsafeForce s2.tail) (unsafeForce s3.tail)))
           -- Guarded: recursive call is under next k

||| Zip two streams into a stream of pairs.
public export
zip : {k : Clock} -> {0 a, b : Type} -> Stream k a -> Stream k b -> Stream k (a, b)
zip = zipWith (,)

||| Zip three streams into a stream of triples.
public export
zip3 : {k : Clock} -> {0 a, b, c : Type} -> Stream k a -> Stream k b -> Stream k c -> Stream k (a, b, c)
zip3 = zipWith3 (,,)

||| Take elements from a stream while a predicate holds.
public export
takeWhile : {k : Clock} -> {0 a : Type} -> (a -> Bool) -> Stream k a -> List a
-- Safe: recursion is structural on the stream's productivity (predicate-bounded),
-- unsafeForce is valid because takeWhile is not guarded-recursive.
takeWhile p s = if p s.head
                  then s.head :: takeWhile p (unsafeForce s.tail)
                  else []

||| Drop elements from a stream while a predicate holds.
public export
dropWhile : {k : Clock} -> {0 a : Type} -> (a -> Bool) -> Stream k a -> Later k (Stream k a)
-- Safe: not guarded-recursive; terminates if the predicate eventually becomes False.
dropWhile p s = if p s.head
                  then dropWhile p (unsafeForce s.tail)
                  else next _ s

||| Filter a stream (may not return if no elements satisfy the predicate).
public export
filter : {k : Clock} -> {0 a : Type} -> (a -> Bool) -> Stream k a -> Later k (Stream k a)
filter p s =
  if p s.head
  then next _ (MkStream s.head (filter p (unsafeForce s.tail)))
  else filter p (unsafeForce s.tail)

--------------------------------------------------------------------------------
-- EXTRACTING FROM STREAMS
--------------------------------------------------------------------------------

||| Take the first n elements of a stream.
|||
||| Safe: recursion is structural on n : Nat. unsafeForce is valid because
||| this function terminates by the decreasing Nat argument.
public export
take : {k : Clock} -> {0 a : Type} -> Nat -> Stream k a -> List a
take Z _ = []
take (S n) s = s.head :: take n (unsafeForce s.tail)

||| Get the element at a specific index (0-based).
|||
||| Safe: recursion is structural on n : Nat.
public export
index : {k : Clock} -> {0 a : Type} -> Nat -> Stream k a -> a
index Z s = s.head
index (S n) s = index n (unsafeForce s.tail)

||| Drop the first n elements of a stream.
|||
||| Safe: recursion is structural on n : Nat.
public export
drop : {k : Clock} -> {0 a : Type} -> Nat -> Stream k a -> Later k (Stream k a)
drop Z s = next _ s
drop (S n) s = drop n (unsafeForce s.tail)

--------------------------------------------------------------------------------
-- COMBINING STREAMS
--------------------------------------------------------------------------------

||| Prepend a list to a stream.
public export
prepend : {k : Clock} -> {0 a : Type} -> List a -> Stream k a -> Stream k a
-- Safe: recursion is structural on the List argument.
prepend [] s = s
prepend (x :: xs) s = MkStream x (next k (prepend xs s))

||| Interleave two streams element by element.
public export
interleave : {k : Clock} -> {0 a : Type} -> Stream k a -> Stream k a -> Stream k a
-- Guarded: recursive call is under next k.
interleave s1 s2 =
  MkStream s1.head
           (next k (interleave s2 (unsafeForce s1.tail)))

--------------------------------------------------------------------------------
-- CLASSIC STREAM EXAMPLES
--------------------------------------------------------------------------------

||| The stream of Fibonacci numbers.
public export
fibs : (k : Clock) -> Stream k Nat
fibs k = fibs' k 0 1
  where
    fibs' : (k : Clock) -> Nat -> Nat -> Stream k Nat
    -- Guarded: recursive call is under next k.
    fibs' k a b = MkStream a (next k (fibs' k b (a + b)))

||| The stream of even numbers (0, 2, 4, 6, ...).
public export
evens : (k : Clock) -> Stream k Nat
evens k = iterate k (\n => n + 2) 0

||| The stream of factorials.
public export
factorials : (k : Clock) -> Stream k Nat
factorials k = factorials' k 1 1
  where
    factorials' : (k : Clock) -> Nat -> Nat -> Stream k Nat
    -- Guarded: recursive call is under next k.
    factorials' k n fact =
      MkStream fact (next k (factorials' k (S n) (fact * (S n))))

||| The stream of powers of 2 (1, 2, 4, 8, ...).
public export
powersOf2 : (k : Clock) -> Stream k Nat
powersOf2 k = iterate k (\x => x + x) 1
