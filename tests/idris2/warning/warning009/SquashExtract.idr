module SquashExtract

import Data.Squash

-- Attempting to extract the witness from a Squash value into a relevant
-- position must be rejected by the IrrelevantUsed check.
-- MkSquash binds its argument as irrelevant (.(x : a)), so x cannot
-- appear in the return value of a function with a non-squash return type.
extract : ‖a‖ -> a
extract (MkSquash x) = x
