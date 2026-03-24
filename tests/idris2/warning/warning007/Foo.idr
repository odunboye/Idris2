module Foo

%deprecate "use newFoo instead"
export
oldFoo : Nat
oldFoo = 42

%deprecate
export
oldBar : Nat
oldBar = 0
