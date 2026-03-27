module Main

-- Example 1: Basic let open syntax
-- This demonstrates the parser support for 'let open' syntax.
-- The syntax is: let open <namespace> in <expression>
-- 
-- Note: This is currently parser-only support. The semantic analysis
-- to actually bring names from the namespace into scope is not yet
-- implemented.
example1 : Int
example1 = let open Data.List in 42

-- Example 2: Opening a different namespace
example2 : Int
example2 = let open Data.Nat in 100

-- Example 3: Using let open with Prelude namespaces
example3 : Int
example3 = let open Prelude.List in 200

-- Example 4: Nested let with open
-- You can nest let open expressions
example4 : Int
example4 = 
  let open Data.List in
    let open Data.Nat in
      300

-- Example 5: let open in a function
-- The open is scoped to the expression after 'in'
example5 : Int -> Int
example5 x = let open Data.List in x + 1

main : IO ()
main = do
  putStrLn "let open syntax examples (parser only)"
  putStrLn "======================================"
  putStrLn "These examples demonstrate that the 'let open' syntax parses correctly."
  putStrLn "Full semantic support (bringing names into scope) is planned."
  putStrLn ""
  putStrLn $ "example1: " ++ show example1
  putStrLn $ "example2: " ++ show example2
  putStrLn $ "example3: " ++ show example3
  putStrLn $ "example4: " ++ show example4
  putStrLn $ "example5 5: " ++ show (example5 5)
