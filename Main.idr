module Main

import Data.List
import Data.Strings
import System
import System.File

import Sat
import Data.DIMACS

-- Test Data

clauses : List Clause
clauses = [
  toClause [MkPos (MkVar 0), MkPos (MkVar 1), MkNeg (MkVar 2)],
  toClause [MkPos (MkVar 1), MkPos (MkVar 2)],
  toClause [MkNeg (MkVar 1)],
  toClause [MkNeg (MkVar 0), MkPos (MkVar 2)]
  ]

main : IO ()
main = do
  (_::fname::_) <- getArgs
  | _ => putStrLn $ "missing input filename"
  (Right cnfText) <- readFile fname
  | Left readErr => putStrLn $ "error reading input file: " ++ show readErr
  case parseDIMACS cnfText of
       Right problem => do
         --printLn problem
         case sat problem.numVars problem.clauses of
              Nothing => putStrLn "unsat"
              Just assignment => do putStrLn "sat"
                                    putStrLn $ unwords $ map showDIMACS assignment
       Left error => putStrLn $ "parsing error: " ++ error
