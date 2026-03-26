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
||| ones : (k : Clock) -> Stream k Nat
||| ones k = MkStream 1 (next k (ones k))
|||
||| -- Map over a guarded value (stays in Later)
||| doubles : {k : Clock} -> Later k Nat -> Later k Nat
||| doubles la = map (2 *) la
||| ```
module Data.Guarded

%default total

--------------------------------------------------------------------------------
-- CLOCKS
--------------------------------------------------------------------------------

||| Clocks index guarded types. The primitive `%Clock` is the type of clocks.
public export
Clock : Type
Clock = %Clock

||| A tick on clock `k` represents the right to access one layer of `Later k`.
||| Ticks are introduced by tick abstraction `\tick k => e`.
|||
||| The constructor `MkTick` is intentionally not exported: ticks must only
||| be obtained via tick abstraction so the type system can enforce guardedness.
export  -- type exported; MkTick is NOT re-exported
data Tick : Clock -> Type where
  ||| Internal use only. Users must obtain ticks via tick abstraction.
  MkTick : (0 k : Clock) -> Tick k

--------------------------------------------------------------------------------
-- THE LATER MODALITY
--------------------------------------------------------------------------------

||| The later modality ▶k A represents a value of type A available after one
||| tick on clock k. This is the core type for guarded recursion.
|||
||| The constructor `MkLater` is not exported: values are introduced via `next`
||| and eliminated via `force` (requiring a tick) or `withTick`.
export  -- type exported; MkLater is NOT re-exported
data Later : Clock -> Type -> Type where
  MkLater : {0 a : Type} -> (k : Clock) -> (1 x : a) -> Later k a

||| Introduce a value into the later modality (delay by one tick on k).
public export
next : {0 a : Type} -> (k : Clock) -> (1 x : a) -> Later k a
next k x = MkLater k x

||| Eliminate a value from the later modality.
|||
||| Requires a tick on k, ensuring that forcing is only done in contexts
||| where k has advanced. In a well-typed guarded recursive program, ticks
||| are only available inside tick abstraction `\tick k => ...`.
public export
force : {0 a : Type} -> {k : Clock} -> Tick k -> Later k a -> a
force _ (MkLater _ x) = x

||| Eliminate a value from the later modality WITHOUT a tick.
|||
||| UNSAFE: only use in structurally-terminating (non-guarded-recursive)
||| contexts such as `take`, `index`, or other functions whose termination
||| is guaranteed by structural recursion on a finite argument (e.g. Nat).
||| Using this in a guarded recursive definition breaks productivity guarantees.
public export
unsafeForce : {0 a : Type} -> {k : Clock} -> Later k a -> a
unsafeForce (MkLater _ x) = x

--------------------------------------------------------------------------------
-- GUARDED FIXPOINT
--------------------------------------------------------------------------------

||| The guarded fixpoint combinator.
|||
||| `fix k f` computes a fixpoint where the recursive result is guarded by
||| `Later k`. The argument `f` must only use its `Later k a` parameter inside
||| `next k` (or other `Later`-producing combinators), which the productivity
||| checker (Core.Termination.Guarded) verifies for user definitions.
|||
||| `fix` itself is an axiomatically trusted primitive: it uses `assert_total`
||| because Idris cannot see the guardedness structurally. Correctness depends
||| on the productivity checker verifying that each call site is guarded.
|||
||| Example:
||| ```idris
||| ones : (k : Clock) -> Later k Nat
||| ones k = fix k (\rec => next k 1)
||| ```
public export
fix : {0 a : Type} -> (k : Clock) -> (Later k a -> a) -> a
fix k f = assert_total (f (MkLater k (fix k f)))

--------------------------------------------------------------------------------
-- FUNCTOR INSTANCE
--------------------------------------------------------------------------------

||| `Later k` is a functor. Mapping a function over a guarded value produces
||| a guarded result; the map is delayed by one tick.
public export
{k : Clock} -> Functor (Later k) where
  map f (MkLater k x) = MkLater k (f x)

--------------------------------------------------------------------------------
-- APPLICATIVE INSTANCE
--------------------------------------------------------------------------------

||| `Later k` is an applicative functor, allowing guarded values to be combined.
|||
||| Example:
||| ```idris
||| addLater : Later k Nat -> Later k Nat -> Later k Nat
||| addLater la lb = (+) <$> la <*> lb
||| ```
public export
{k : Clock} -> Applicative (Later k) where
  pure x = MkLater _ x
  (MkLater k f) <*> (MkLater _ x) = MkLater k (f x)

||| Lift a binary function to guarded values.
public export
liftA2 : {k : Clock} -> (a -> b -> c) -> Later k a -> Later k b -> Later k c
liftA2 f (MkLater k x) (MkLater _ y) = MkLater k (f x y)

||| Lift a ternary function to guarded values.
public export
liftA3 : {k : Clock} -> (a -> b -> c -> d) -> Later k a -> Later k b -> Later k c -> Later k d
liftA3 f (MkLater k x) (MkLater _ y) (MkLater _ z) = MkLater k (f x y z)

||| Join a double-guarded value: Later k (Later k a) -> Later k a.
||| One tick suffices since both layers share the same clock.
public export
join : {0 a : Type} -> {k : Clock} -> Later k (Later k a) -> Later k a
join (MkLater k (MkLater _ x)) = MkLater k x

--------------------------------------------------------------------------------
-- NOTE: Later k is NOT a Monad in general.
--
-- The bind operation `la >>= f` would require forcing `la` to feed its value
-- into `f`, and then forcing the result of `f`. This uses `force` twice without
-- a tick, which is unsound for guarded recursive types. Later k is applicative
-- (and has a join as above), but monadic bind is not valid for arbitrary clocks
-- in the Atkey-McBride framework.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- TICK UTILITIES
--------------------------------------------------------------------------------

||| Apply a function that needs a tick, returning a guarded value.
|||
||| This is the primary way to stay "inside Later" while doing work that
||| requires a tick:
|||
||| ```idris
||| mapWithTick : {k : Clock} -> (a -> b) -> Later k a -> Later k b
||| mapWithTick f la = withTick (\t => f (force t la))
||| ```
public export
withTick : {0 a : Type} -> {k : Clock} -> (Tick k -> a) -> Later k a
withTick {k} f = MkLater k (f (MkTick k))

||| Sequence a guarded computation with a function that needs the result and a tick.
public export
andThen : {0 a, b : Type} -> {k : Clock} -> Later k a -> (a -> Tick k -> b) -> Later k b
andThen {k} la f = MkLater k (f (unsafeForce la) (MkTick k))

||| Create a guarded computation that depends on a tick.
public export
tickBind : {0 a, b : Type} -> {k : Clock} -> (Tick k -> Later k a) -> (a -> b) -> Later k b
tickBind {k} tf g = MkLater k (g (unsafeForce (tf (MkTick k))))

--------------------------------------------------------------------------------
-- TRAVERSABLE-LIKE FUNCTIONS
--------------------------------------------------------------------------------

||| Sequence a list of guarded values into a guarded list.
public export
sequence : {k : Clock} -> List (Later k a) -> Later k (List a)
sequence [] = pure []
sequence (la :: las) = (::) <$> la <*> sequence las

||| Map a function producing guarded values over a list and sequence the results.
public export
traverse : {k : Clock} -> (a -> Later k b) -> List a -> Later k (List b)
traverse f [] = pure []
traverse f (x :: xs) = (::) <$> f x <*> traverse f xs

||| Zip two guarded values together.
public export
zip : {k : Clock} -> Later k a -> Later k b -> Later k (a, b)
zip (MkLater k x) (MkLater _ y) = MkLater k (x, y)

||| Zip three guarded values together.
public export
zip3 : {k : Clock} -> Later k a -> Later k b -> Later k c -> Later k (a, b, c)
zip3 (MkLater k x) (MkLater _ y) (MkLater _ z) = MkLater k (x, y, z)

--------------------------------------------------------------------------------
-- BOOLEAN OPERATIONS
--------------------------------------------------------------------------------

||| Boolean conjunction (AND) for guarded booleans.
public export
andLater : {k : Clock} -> Later k Bool -> Later k Bool -> Later k Bool
andLater (MkLater k x) (MkLater _ y) = MkLater k (x && y)

||| Boolean disjunction (OR) for guarded booleans.
public export
orLater : {k : Clock} -> Later k Bool -> Later k Bool -> Later k Bool
orLater (MkLater k x) (MkLater _ y) = MkLater k (x || y)

||| Conditional for guarded booleans.
public export
ifLater : {k : Clock} -> Later k Bool -> Later k a -> Later k a -> Later k a
ifLater (MkLater k b) (MkLater _ t) (MkLater _ f) = MkLater k (if b then t else f)

||| Negation for guarded booleans.
public export
notLater : {k : Clock} -> Later k Bool -> Later k Bool
notLater = map not

--------------------------------------------------------------------------------
-- UTILITY FUNCTIONS
--------------------------------------------------------------------------------

||| Delay a pure value by one tick. Alias for `pure` from the Applicative instance.
public export
delay : {0 a : Type} -> {k : Clock} -> a -> Later k a
delay = pure

||| Fold a list using a guarded combining function.
public export
foldrLater : {k : Clock} -> (a -> Later k b -> Later k b) -> Later k b -> List a -> Later k b
foldrLater f z [] = z
foldrLater f z (x :: xs) = f x (foldrLater f z xs)

||| Apply a binary operator to two guarded values.
public export
liftOp : {k : Clock} -> (a -> b -> c) -> Later k a -> Later k b -> Later k c
liftOp f (MkLater k x) (MkLater _ y) = MkLater k (f x y)

||| Apply a unary operator to a guarded value. Alias for `map`.
public export
liftOp1 : {k : Clock} -> (a -> b) -> Later k a -> Later k b
liftOp1 = map
