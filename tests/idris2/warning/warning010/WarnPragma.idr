module WarnPragma

-- %warning emits a custom message at every use site.

%warning "oldAdd is superseded by newAdd"
export
oldAdd : Nat -> Nat -> Nat
oldAdd = (+)

export
newAdd : Nat -> Nat -> Nat
newAdd = (+)

-- Use it — should trigger the warning
export
result : Nat
result = oldAdd 3 4
