module Data.DIMACS

import Data.List
import Data.Strings

import Text.Lexer
import Text.Parser

import Sat

%default total

public export
record CNFProblem where
  constructor MkCNFProblem
  numVars : Int
  numClauses : Int
  clauses : List Clause

export
Show CNFProblem where
  show prob = "CNF Problem (" ++ show prob.numVars ++ " vars, " ++ show prob.numClauses ++ " clauses):\n" ++
              show prob.clauses

data Token = Comment
           | Problem String
           | Zero
           | Lit String

Show Token where
  show Comment = "(comment)"
  show (Problem s) = "(problem: " ++ s ++ ")"
  show Zero = "0"
  show (Lit s) = s

comment : Lexer
comment = is 'c' <+> many (pred (/= '\n')) <+> is '\n' <+> many space

problem : Lexer
problem = is 'p' <+> is ' ' <+> many (pred (/= '\n')) <+> is '\n' <+> many space

zero : Lexer
zero = is '0' <+> many space

lit : Lexer
lit = opt (is '-') <+> some digit <+> some space

tokenMap : TokenMap Token
tokenMap = [
  (comment, \_ => Comment),
  (problem, Problem . trim),
  (zero, \_ => Zero),
  (lit, Lit . trim)
  ]

lexDimacs : String -> Either String (List Token)
lexDimacs s = let (toks, line, col, remainder) = lex tokenMap s in
                  if remainder == "" then Right $ map tok toks
                                     else Left $ "remaining: " ++ remainder

Parser : Type -> Type
Parser a = Grammar Token True a

isProblem : Token -> Maybe CNFProblem
isProblem (Problem s) = case words s of
                             ["p", "cnf", nVars, nClauses] =>
                               let numVars = cast nVars
                                   numClauses = cast nClauses in
                                     Just $ MkCNFProblem numVars numClauses []
                             _ => Nothing

isProblem _ = Nothing

literal : Token -> Maybe Sat.Lit
literal (Lit s) = let i = cast {to=Int} s in
                      if i > 0 then Just $ MkPos (MkVar (i-1))
                      else if i < 0 then Just $ MkNeg (MkVar ((-i) - 1))
                      else Nothing
literal _ = Nothing

isZero : Token -> Maybe ()
isZero Zero = Just ()
isZero _ = Nothing

isComment : Token -> Maybe ()
isComment Comment = Just ()
isComment _ = Nothing

parseClause : Parser (Maybe Clause)
parseClause = do
  lits <- many (terminal "literal" literal) <* terminal "zero" isZero
  many $ terminal "comment" isComment
  id $ case lits of
            [] => fatalError "empty clause can not be satisfied"
            (c::cs) => pure $ Just $ toClause (c::cs)

parseCNF : Parser CNFProblem
parseCNF = do
  many $ terminal "initial comment" isComment
  initState <- terminal "CNF problem header" isProblem
  parsedClauses <- some parseClause
  pure $ record { clauses = mapMaybe id parsedClauses } initState

showError : ParseError Token -> String
showError (Error e toks) = "parse error: " ++ e ++ "\nnext tokens: " ++ show toks

export
parseDIMACS : String -> Either String CNFProblem
parseDIMACS s = do
  toks <- lexDimacs s
  (parsed, toks) <- the (Either String (CNFProblem, List Token)) $ either (Left . showError) Right $ parse parseCNF toks
  Right parsed

export
showDIMACS : (Var, Bool) -> String
showDIMACS (MkVar d, True) = show (d+1)
showDIMACS (MkVar d, False) = show (-(d+1))
