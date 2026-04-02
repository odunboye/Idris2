module ForwardDecl

-- isEven is forward-declared here; its body comes below isOdd.
-- This enables mutual recursion without a `mutual` block.
isEven : Nat -> Bool

isOdd : Nat -> Bool
isOdd Z = False
isOdd (S n) = isEven n

-- Body for the forward declaration: fills in the None entry.
isEven Z = True
isEven (S n) = isOdd n

main : IO ()
main = do
  printLn (isEven 4)  -- True
  printLn (isOdd 3)   -- True
  printLn (isEven 7)  -- False
