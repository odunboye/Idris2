module Debug.Trace

import Prelude
import PrimIO

%default total

export
trace : (msg : String) -> (result : a) -> a
trace x val = unsafePerformIO (do putStrLn x; pure val)

||| Print a trace message in an `IO`-like context.
|||
||| Unlike `trace`, this does not use `unsafePerformIO` and is safe to use
||| inside `IO` (or any `HasIO`) computations without totality conflicts.
export
traceIO : HasIO io => (msg : String) -> io ()
traceIO msg = putStrLn msg

||| Print a trace message derived from the given value, then return the value.
|||
||| `IO`-safe counterpart to `traceValBy`.
export %inline
traceIOValBy : HasIO io => (msgF : a -> String) -> (val : a) -> io a
traceIOValBy f v = do traceIO (f v); pure v

||| Print a showable value as a trace message, then return it.
|||
||| `IO`-safe counterpart to `traceVal`.
export %inline
traceIOVal : HasIO io => Show a => a -> io a
traceIOVal = traceIOValBy show

export %inline
traceValBy : (msgF : a -> String) -> (result : a) -> a
traceValBy f v = trace (f v) v

export %inline
traceVal : Show a => a -> a
traceVal = traceValBy show
