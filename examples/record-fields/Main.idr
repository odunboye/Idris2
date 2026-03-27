module Main

import Person
import Company

-- Use qualified field names to disambiguate
getPersonName : Person -> String
getPersonName = Person.name

getCompanyName : Company -> String
getCompanyName = Company.name

main : IO ()
main = do
  let person = MkPerson "Alice" 30
  let company = MkCompany "Acme" 100
  printLn $ "Person: " ++ getPersonName person
  printLn $ "Company: " ++ getCompanyName company
