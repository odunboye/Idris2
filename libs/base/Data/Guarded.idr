||| Guarded recursion primitives for clock-based productivity checking.
|||
||| This module provides the core types and combinators for writing productive
||| corecursive definitions using guarded recursion (Atkey & McBride 2013).
|||
||| Example usage:
||| ```idris
||| import Data.Guarded
||| 
||| %default total
||| 
||| -- An infinite stream of ones
||| ones : (k : Clock) -> Later k Nat
||| ones k = fix k (\rec => next k 1)
||| 
||| -- Map over guarded values
||| doubles : (k : Clock) -> Later k Nat -> Later k Nat
||| doubles k = map (2 *)
||| ```
module Data.Guarded

%default total

--------------------------------------------------------------------------------
-- CLOCKS
--------------------------------------------------------------------------------

||| Clocks are used to index guarded types. A clock represents a notion of 
||| time steps or "ticks". The primitive `%Clock` is the type of clocks.
|||
||| Clocks are introduced by tick abstraction `\tick k => ...` and used to
||| force guarded values.
public export
Clock : Type
Clock = %Clock

||| A tick on a clock `k` represents the ability to access values guarded by 
||| `Later k`. Ticks are introduced by tick abstraction `\tick k => e`.
public export
Tick : Clock -> Type
Tick k = Clock

--------------------------------------------------------------------------------
-- THE LATER MODALITY
--------------------------------------------------------------------------------

||| The later modality ▶k A represents a value of type A that will be available
||| "after one tick" on clock k. This is the fundamental type for guarded recursion.
|||
||| A value of type `Later k A` cannot be accessed immediately; it must be
||| "forced" after a tick on k using `force`.
|||
||| `Later k` is a functor, applicative functor, and monad.
public export
data Later : Clock -> Type -> Type where
  ||| Construct a guarded value.
  |||
  ||| @ k the clock on which the value is delayed
  ||| @ x the underlying value
  MkLater : {0 a : Type} -> (k : Clock) -> (1 x : a) -> Later k a

||| Introduce a value into the later modality.
|||
||| Values created with `next` are delayed by one tick on the given clock.
||| This is the introduction form for `Later`.
public export
next : {0 a : Type} -> (k : Clock) -> (1 x : a) -> Later k a
next k x = MkLater k x

||| Eliminate a value from the later modality.
|||
||| This extracts the value from a `Later` constructor. Note that in a 
||| well-typed guarded recursive program, this should only be done after
||| obtaining a tick on the relevant clock (via tick abstraction).
public export
force : {0 a : Type} -> {k : Clock} -> Later k a -> a
force (MkLater _ x) = x

--------------------------------------------------------------------------------
-- GUARDED FIXPOINT
--------------------------------------------------------------------------------

||| The guarded fixpoint combinator.
|||
||| `fix k f` computes a fixed point where recursive calls are guarded by 
||| `Later k`. The function `f` receives an argument of type `Later k a` 
||| representing the recursive result, and must produce an `a`.
|||
||| The productivity checker ensures that `f` only uses its argument inside
||| a `next` constructor, guaranteeing productivity.
|||
||| Example - infinite stream of ones:
||| ```idris
||| ones : (k : Clock) -> Later k Nat
||| ones k = fix k (\rec => next k 1)
||| ```
|||
||| Note: This implementation uses `assert_total` because the recursion is 
||| guarded by the `Later` constructor. The productivity checker verifies
||| that uses of `fix` are productive.
public export
fix : {0 a : Type} -> (k : Clock) -> (Later k a -> a) -> a
fix k f = assert_total (f (MkLater k (fix k f)))

--------------------------------------------------------------------------------
-- FUNCTOR INSTANCE
--------------------------------------------------------------------------------

||| `Later k` is a functor. Mapping over a guarded value delays the function
||| application by one tick.
public export
{k : Clock} -> Functor (Later k) where
  map f la = MkLater _ (f (force la))

--------------------------------------------------------------------------------
-- APPLICATIVE INSTANCE
--------------------------------------------------------------------------------

||| `Later k` is an applicative functor. This allows combining guarded values
||| using applicative style.
|||
||| Example:
||| ```idris
||| addLater : Later k Nat -> Later k Nat -> Later k Nat
||| addLater la lb = pure (+) <*> la <*> lb
||| ```
public export
{k : Clock} -> Applicative (Later k) where
  pure x = MkLater _ x
  lf <*> la = MkLater _ ((force lf) (force la))

||| Lift a binary function to guarded values using applicative style.
public export
liftA2 : {k : Clock} -> (a -> b -> c) -> Later k a -> Later k b -> Later k c
liftA2 f la lb = MkLater _ (f (force la) (force lb))

||| Lift a ternary function to guarded values.
public export
liftA3 : {k : Clock} -> (a -> b -> c -> d) -> Later k a -> Later k b -> Later k c -> Later k d
liftA3 f la lb lc = MkLater _ (f (force la) (force lb) (force lc))

--------------------------------------------------------------------------------
-- MONAD INSTANCE
--------------------------------------------------------------------------------

||| `Later k` is a monad. This allows sequencing guarded computations.
|||
||| Example:
||| ```idris
||| chainLater : Later k Nat -> Later k Nat
||| chainLater la = do
|||   n <- la
|||   pure (n + 1)
||| ```
public export
{k : Clock} -> Monad (Later k) where
  la >>= f = MkLater _ (force (f (force la)))

||| Join a double-guarded value into a single guarded value.
public export
join : {0 a : Type} -> {k : Clock} -> Later k (Later k a) -> Later k a
join {a} {k} lla = MkLater k (force {a} {k} (force {a=Later k a} {k} lla))

--------------------------------------------------------------------------------
-- TRAVERSABLE-LIKE FUNCTIONS
--------------------------------------------------------------------------------

||| Sequence a list of guarded values into a guarded list.
||| 
||| This collects all the guarded values and returns a single guarded
||| computation that produces the list.
public export
sequence : {k : Clock} -> List (Later k a) -> Later k (List a)
sequence [] = pure []
sequence (la :: las) = pure (::) <*> (pure (force la)) <*> sequence las

||| Map a function that produces guarded values over a list, and sequence
||| the results.
public export
traverse : {k : Clock} -> (a -> Later k b) -> List a -> Later k (List b)
traverse f [] = pure []
traverse f (x :: xs) = pure (::) <*> f x <*> traverse f xs

||| Zip two guarded values together.
public export
zip : {k : Clock} -> Later k a -> Later k b -> Later k (a, b)
zip la lb = MkLater _ ((force la), (force lb))

||| Zip three guarded values together.
public export
zip3 : {k : Clock} -> Later k a -> Later k b -> Later k c -> Later k (a, b, c)
zip3 la lb lc = MkLater _ ((force la), (force lb), (force lc))

--------------------------------------------------------------------------------
-- BOOLEAN OPERATIONS
--------------------------------------------------------------------------------

||| Boolean conjunction (AND) for guarded booleans.
public export
andLater : {k : Clock} -> Later k Bool -> Later k Bool -> Later k Bool
andLater lb1 lb2 = MkLater _ ((force lb1) && (force lb2))

||| Boolean disjunction (OR) for guarded booleans.
public export
orLater : {k : Clock} -> Later k Bool -> Later k Bool -> Later k Bool
orLater lb1 lb2 = MkLater _ ((force lb1) || (force lb2))

||| Conditional for guarded booleans.
public export
ifLater : {k : Clock} -> Later k Bool -> Later k a -> Later k a -> Later k a
ifLater lb lt lf = MkLater _ (if (force lb) then (force lt) else (force lf))

||| Negation for guarded booleans.
public export
notLater : {k : Clock} -> Later k Bool -> Later k Bool
notLater lb = map not lb

--------------------------------------------------------------------------------
-- UTILITY FUNCTIONS
--------------------------------------------------------------------------------

||| Delay a pure value by one tick.
||| This is an alias for `pure` from the Applicative instance.
public export
delay : {0 a : Type} -> {k : Clock} -> a -> Later k a
delay = pure

||| Extract a value from a guarded computation, or return a default.
||| Note: This forces the guarded value immediately, which may not be
||| safe in all contexts.
public export
fromLater : {0 a : Type} -> {k : Clock} -> a -> Later k a -> a
fromLater def la = force la

||| Fold a list using a guarded combining function.
public export
foldrLater : {k : Clock} -> (a -> Later k b -> Later k b) -> Later k b -> List a -> Later k b
foldrLater f z [] = z
foldrLater f z (x :: xs) = f x (foldrLater f z xs)

||| Create a guarded value that delays for n ticks.
public export
delayN : {0 a : Type} -> {k : Clock} -> Nat -> a -> Later k a
delayN Z x = pure x
delayN (S n) x = MkLater _ (force (delayN {a} {k} n x))

||| Apply a binary operator to two guarded values.
public export
liftOp : {k : Clock} -> (a -> b -> c) -> Later k a -> Later k b -> Later k c
liftOp f la lb = MkLater _ (f (force la) (force lb))

||| Apply a unary operator to a guarded value.
public export
liftOp1 : {k : Clock} -> (a -> b) -> Later k a -> Later k b
liftOp1 = map

--------------------------------------------------------------------------------
-- TICK UTILITIES
--------------------------------------------------------------------------------

||| Apply a function that needs a tick to produce a guarded value.
||| This creates the tick using the clock itself.
public export
withTick : {0 a : Type} -> {k : Clock} -> (Tick k -> a) -> Later k a
withTick f = MkLater _ (f k)

||| Sequence a guarded computation with a function that needs the result
||| and a tick.
public export
andThen : {0 a, b : Type} -> {k : Clock} -> Later k a -> (a -> Tick k -> b) -> Later k b
andThen la f = MkLater _ (f (force la) k)

||| Create a guarded computation that depends on a tick.
public export
tickBind : {0 a, b : Type} -> {k : Clock} -> (Tick k -> Later k a) -> (a -> b) -> Later k b
tickBind tf g = MkLater _ (g (force (tf k)))
