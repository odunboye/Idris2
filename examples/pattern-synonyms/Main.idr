module Main

-- Simple pattern synonyms (no arguments)
pattern OK = 200
pattern NotFound = 404
pattern Error = 500

-- Pattern synonym with one argument
pattern Single x = [x]

-- Pattern synonym with two arguments
pattern Pair a b = (a, b)

-- Pattern synonym for list cons (using different names to avoid conflict)
pattern MyCons x xs = (::) x xs
pattern MyNil = []

-- Using pattern synonyms in function definitions
isSuccess : Int -> Bool
isSuccess OK = True
isSuccess _ = False

getFirst : List Int -> Int
getFirst (MyCons x _) = x
getFirst MyNil = 0

getFirstPair : (Int, Int) -> Int
getFirstPair (Pair x _) = x

-- Pattern synonyms can be used in case expressions
describe : Int -> String
describe code = case code of
  OK => "Success"
  NotFound => "Not found"
  Error => "Server error"
  _ => "Unknown"

main : IO ()
main = do
  putStrLn "Pattern Synonym Examples"
  putStrLn "========================"
  putStrLn $ "isSuccess 200: " ++ show (isSuccess 200)
  putStrLn $ "isSuccess 404: " ++ show (isSuccess 404)
  putStrLn $ "describe 200: " ++ describe 200
  putStrLn $ "describe 500: " ++ describe 500
  putStrLn $ "getFirst [1,2,3]: " ++ show (getFirst [1, 2, 3])
  putStrLn $ "getFirst []: " ++ show (getFirst [])
  putStrLn $ "getFirstPair (10,20): " ++ show (getFirstPair (10, 20))
