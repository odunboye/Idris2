module SafeModule

%safe

-- believe_me should be banned in a safe module
bad : Nat -> String
bad n = believe_me n
