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
||| This ensures that corecursive definitions producing streams are productive -
||| the tail can only be accessed after a tick on k.
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

-- Note: Using 'record' instead of 'data' works around the strict positivity
-- issue because records have different positivity checking rules.

--------------------------------------------------------------------------------
-- CREATING STREAMS
--------------------------------------------------------------------------------

||| Create a stream from a head and a guarded tail.
|||
||| This is a convenience alias for the MkStream constructor.
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
repeat k x = MkStream x (assert_total (next k (repeat k x)))

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
iterate k f x = MkStream x (assert_total (next k (iterate k f (f x))))

||| Generate a stream from a seed value and a generator function.
|||
||| The generator produces both the next element and the next seed.
public export
unfold : {0 a, s : Type} -> 
         (k : Clock) -> (s -> (a, s)) -> s -> Stream k a
unfold k f s = 
  let (x, s') = f s in
  MkStream x (assert_total (next k (unfold k f s')))

||| Create a stream by counting up from a starting number.
public export
countFrom : (k : Clock) -> Nat -> Stream k Nat
countFrom k n = assert_total (iterate k S n)

||| Create a stream of natural numbers starting from 0.
public export
nats : (k : Clock) -> Stream k Nat
nats k = assert_total (countFrom k 0)

--------------------------------------------------------------------------------
-- TRANSFORMING STREAMS
--------------------------------------------------------------------------------

||| Map a function over every element of a stream.
public export
map : {k : Clock} -> {0 a, b : Type} -> (a -> b) -> Stream k a -> Stream k b
map f s = MkStream (f s.head) (assert_total (next k (map f (force s.tail))))

||| Zip two streams together element-wise.
public export
zipWith : {k : Clock} -> {0 a, b, c : Type} -> 
          (a -> b -> c) -> Stream k a -> Stream k b -> Stream k c
zipWith f s1 s2 = 
  MkStream (f s1.head s2.head) 
           (assert_total (next k (zipWith f (force s1.tail) (force s2.tail))))

||| Zip three streams together element-wise.
public export
zipWith3 : {k : Clock} -> {0 a, b, c, d : Type} -> 
           (a -> b -> c -> d) -> Stream k a -> Stream k b -> Stream k c -> Stream k d
zipWith3 f s1 s2 s3 = 
  MkStream (f s1.head s2.head s3.head)
           (assert_total (next k (zipWith3 f (force s1.tail) (force s2.tail) (force s3.tail))))

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
takeWhile p s = if p s.head 
                  then s.head :: assert_total (takeWhile p (force s.tail))
                  else []

||| Drop elements from a stream while a predicate holds.
public export
dropWhile : {k : Clock} -> {0 a : Type} -> (a -> Bool) -> Stream k a -> Later k (Stream k a)
dropWhile p s = if p s.head
                  then assert_total (dropWhile p (force s.tail))
                  else next _ s

||| Filter a stream (lazily - may not return if no elements satisfy predicate).
public export
filter : {k : Clock} -> {0 a : Type} -> (a -> Bool) -> Stream k a -> Later k (Stream k a)
filter p s = 
  if p s.head 
  then next _ (MkStream s.head (assert_total (filter p (force s.tail))))
  else assert_total (filter p (force s.tail))

--------------------------------------------------------------------------------
-- EXTRACTING FROM STREAMS
--------------------------------------------------------------------------------

||| Take the first n elements of a stream.
|||
||| This requires n ticks on the clock to access the elements.
public export
take : {k : Clock} -> {0 a : Type} -> Nat -> Stream k a -> List a
take Z _ = []
take (S n) s = s.head :: take n (force s.tail)

||| Get the element at a specific index (0-based).
|||
||| This requires n+1 ticks on the clock.
public export
index : {k : Clock} -> {0 a : Type} -> Nat -> Stream k a -> a
index Z s = s.head
index (S n) s = index n (force s.tail)

||| Drop the first n elements of a stream.
public export
drop : {k : Clock} -> {0 a : Type} -> Nat -> Stream k a -> Later k (Stream k a)
drop Z s = next _ s
drop (S n) s = assert_total (drop n (force s.tail))

--------------------------------------------------------------------------------
-- COMBINING STREAMS
--------------------------------------------------------------------------------

||| Prepend a list to a stream.
public export
prepend : {k : Clock} -> {0 a : Type} -> List a -> Stream k a -> Stream k a
prepend [] s = s
prepend (x :: xs) s = MkStream x (assert_total (next k (prepend xs s)))

||| Interleave two streams element by element.
public export
interleave : {k : Clock} -> {0 a : Type} -> Stream k a -> Stream k a -> Stream k a
interleave s1 s2 = 
  MkStream s1.head 
           (assert_total (next k (interleave s2 (force s1.tail))))

--------------------------------------------------------------------------------
-- CLASSIC STREAM EXAMPLES
--------------------------------------------------------------------------------

||| The stream of Fibonacci numbers.
||| 
||| Uses a recursive definition with two accumulators.
||| Note: Uses assert_total because the productivity checker doesn't recognize
||| that the recursive call is guarded by next.
public export
fibs : (k : Clock) -> Stream k Nat
fibs k = fibs' k 0 1
  where
    fibs' : (k : Clock) -> Nat -> Nat -> Stream k Nat
    fibs' k a b = MkStream a (assert_total (next k (fibs' k b (a + b))))

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
    factorials' k n fact = 
      MkStream fact (assert_total (next k (factorials' k (S n) (fact * (S n)))))

||| The stream of powers of 2 (1, 2, 4, 8, ...).
public export
powersOf2 : (k : Clock) -> Stream k Nat
powersOf2 k = iterate k (\x => x + x) 1
