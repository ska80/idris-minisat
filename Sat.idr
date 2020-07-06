module Sat

import Data.List
import Data.Maybe
import Data.Strings

import Data.Linear.Array

import Control.Linear
import Control.Linear.LState

%default total

public export
data Var = MkVar Int
export
Show Var where
  show (MkVar n) = show n

public export
data Lit = MkPos Var | MkNeg Var
export
Show Lit where
  show (MkPos v) = " " ++ show v
  show (MkNeg v) = "~" ++ show v

isPos : Lit -> Bool
isPos (MkPos _) = True
isPos (MkNeg _) = False

getVar : Lit -> Var
getVar (MkPos v) = v
getVar (MkNeg v) = v

export
data Clause : Type where
  MkClause : (l : List Lit) -> {auto ok : NonEmpty l} -> Clause

export
toClause : (l : List Lit) -> {auto ok : NonEmpty l} -> Clause
toClause l {ok} = MkClause l {ok}

export
Show Clause where
  show (MkClause l) = show l

Watchlist : Type
Watchlist = LinArray (List Clause)

litIndex : Lit -> Int
litIndex (MkPos (MkVar n)) = 2 * n
litIndex (MkNeg (MkVar n)) = 2 * n + 1

initWatchlist : Int -> List Clause -> Watchlist
initWatchlist maxLit clauses = newArray maxLit (initWatchlist' clauses)
  where
    initWatchlist' : List Clause -> (1 a : Watchlist) -> Watchlist
    initWatchlist' [] a = a
    initWatchlist' (c@(MkClause ls {ok})::cs) a =
      let firstLit = head ls
          idx = litIndex firstLit
          (r # arr') = mread a idx in
          initWatchlist' cs $ write arr' idx (c::(fromMaybe [] r))

getWatched : Lit -> LState Watchlist (List Clause)
getWatched lit = do
  v <- run (\wl => mread wl (litIndex lit))
  pure $ fromMaybe [] v

removeWatches : Lit -> LState Watchlist ()
removeWatches lit = do
  change $ \wl => write wl (litIndex lit) []

addWatch : Lit -> Clause -> LState Watchlist ()
addWatch l c = do
  clauses <- getWatched l
  change $ \wl => write wl (litIndex l) (c::clauses)

addWatches : List (Lit, Clause) -> LState Watchlist ()
addWatches ls = traverse_ (uncurry addWatch) ls

Assignments : Type
Assignments = LinArray (Maybe Bool)

varIndex : Var -> Int
varIndex (MkVar n) = n

value : Var -> LState Assignments (Maybe Bool)
value var = do
  val <- run $ (\as => mread as (varIndex var))
  pure $ fromMaybe Nothing val

assign : Var -> Bool -> LState Assignments ()
assign var v = change (\as => write as (varIndex var) (Just v))

unassign : Var -> LState Assignments ()
unassign var = change (\as => write as (varIndex var) Nothing)

SolverState : Type -> Type
SolverState = LState (Watchlist, Assignments)

dumpAs' : Array arr => Int -> List (Var, Maybe Bool) -> arr (Maybe Bool) -> List (Var, Maybe Bool)
dumpAs' i s as =
  let sz = size as in
      if i >= sz then reverse s
                 else case read as i of
                           Nothing => dumpAs' (assert_smaller i (i+1)) ((MkVar i, Nothing)::s) as
                           Just e => dumpAs' (assert_smaller i (i+1)) ((MkVar i, e)::s) as

dumpArr : (1 _ : Assignments) -> List (Var, Maybe Bool)
dumpArr as = toIArray as (dumpAs' 0 [])

initAssignments : Int -> Assignments
initAssignments n = newArray n (initAssignments' (integerToNat $ cast n)) where
  initAssignments' : Nat -> (1 _ : Assignments) -> Assignments
  initAssignments' Z as = as
  initAssignments' (S n) as = write (initAssignments' n as) (cast n) Nothing

updateWatchlist : Lit -> SolverState Bool
updateWatchlist assignFalse = do
  needUpdate <- liftSt $ getWatched assignFalse
  case needUpdate of
       [] => pure True
       needUpdate => do
         (Just alts) <- liftSt $ lfoldlM findAlt (Just []) needUpdate
         | Nothing => pure False
         liftSt $ removeWatches assignFalse
         liftSt $ addWatches alts
         pure True

    where

  altOk : List Lit -> LState Assignments (Maybe Lit)
  altOk [] = pure Nothing
  altOk (l::ls) = case !(value (getVar l)) of
                         Just x => if x == isPos l then pure $ Just l
                                                   else altOk ls
                         Nothing => pure $ Just l

  findAlt : (Maybe (List (Lit, Clause))) -> (_ : Clause) -> LState Assignments (Maybe (List (Lit, Clause)))
  findAlt Nothing _ = pure Nothing
  findAlt (Just acc) (MkClause ls) = do
    (Just foundAlt) <- altOk ls
    | Nothing => pure Nothing
    pure $ Just ((foundAlt, MkClause ls)::acc)

mutual
  solveTry : Bool -> Var -> SolverState Bool
  solveTry a var = do
    liftSt $ assign var a
    ok <- updateWatchlist (if a then MkNeg var else MkPos var)
    if ok then pure True
          else do liftSt $ unassign var
                  pure False

  solve : Int -> Int -> SolverState Bool
  solve numVars d = if d >= numVars then pure True else do
    tryValues [False, True]
    where
      var : Var
      var = MkVar d

      tryValues : List Bool -> SolverState Bool
      tryValues [] = pure False
      tryValues (val::rest) = do
        couldBe <- solveTry val var
        if couldBe
           then do
             whenIsVal <- solve numVars (assert_smaller d (d+1))
             if whenIsVal then pure True
                          else do
                            liftSt $ unassign var
                            if val then pure False
                                   else tryValues rest
           else if val then pure False
           else tryValues rest

export
sat : Int -> List Clause -> Maybe (List (Var, Bool))
sat numVars clauses =
  let wl = initWatchlist (2 * numVars) clauses
      as = initAssignments numVars
      (r # (wl', as')) = runLState (wl, as) (solve numVars 0) in
      if r then traverse result (dumpArr as')
           else Nothing
  where
    result : (Var, Maybe Bool) -> Maybe (Var, Bool)
    result (v, Just a) = Just (v, a)
    result (_, Nothing) = Nothing
