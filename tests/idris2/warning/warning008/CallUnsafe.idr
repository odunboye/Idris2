module CallUnsafe

import UnsafeAnnotation

%safe

-- Calling an %unsafe function from a safe module should be an error
bad : Nat
bad = dangerousFn
