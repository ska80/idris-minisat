module Main

import Data.List
import Data.Strings
import System
import System.File

import Sat
import Data.DIMACS

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
