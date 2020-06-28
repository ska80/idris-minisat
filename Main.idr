module Main

import Data.List

import Sat

-- Test Data

clauses : List Clause
clauses = [
  toClause [MkPos (MkVar 0), MkPos (MkVar 1), MkNeg (MkVar 2)],
  toClause [MkPos (MkVar 1), MkPos (MkVar 2)],
  toClause [MkNeg (MkVar 1)],
  toClause [MkNeg (MkVar 0), MkPos (MkVar 2)]
  ]

main : IO ()
main = putStrLn $ show $ sat 3 clauses
