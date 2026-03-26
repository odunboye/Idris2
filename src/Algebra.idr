module Algebra

import public Algebra.Preorder
import public Algebra.Semiring
import public Algebra.ZeroOneOmega

%default total

public export
RigCount : Type
RigCount = ZeroOneOmega

export
showCount : RigCount -> String
showCount = elimSemi "0 " "1 " (const "")
