module Sat

import Data.List
import Data.Maybe
import Data.Strings

import Data.Linear.Array

%default total

interface LFoldableA (t : Type -> Type) where
  lfoldra : (func : ((_ : elem) -> (1 _ : acc) -> acc)) -> (1 init : acc) -> (input : t elem) -> acc

LFoldableA List where
  lfoldra f acc [] = acc
  lfoldra f acc (x::xs) = f x $ lfoldra f acc xs

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

Show Clause where
  show (MkClause l) = show l

Watchlist : Type
Watchlist = LinArray (List Clause)

litIndex : Lit -> Int
litIndex (MkPos (MkVar n)) = 2 * n
litIndex (MkNeg (MkVar n)) = 2 * n + 1

initWatchlist : Int -> List Clause -> LinArray (List Clause)
initWatchlist maxLit clauses = newArray maxLit (initWatchlist' clauses)
  where
    initWatchlist' : List Clause -> (1 a : Watchlist) -> Watchlist
    initWatchlist' [] a = a
    initWatchlist' (c@(MkClause ls {ok})::cs) a =
      let firstLit = head ls
          idx = litIndex firstLit
          (r # arr') = mread a idx in
          initWatchlist' cs $ write arr' idx (c::(fromMaybe [] r))

getWatched : (1 _ : Watchlist) -> Lit -> LPair (List Clause) Watchlist
getWatched wl lit = let (v # wl') = mread wl (litIndex lit) in
                        ((fromMaybe [] v) # wl')

removeWatches : (1 _ : Watchlist) -> Lit -> Watchlist
removeWatches wl lit = write wl (litIndex lit) []

addWatches : (1 _ : Watchlist) -> List (Lit, Clause) -> Watchlist
addWatches wl [] = wl
addWatches wl ((l, c)::rest) =
  let (clauses # wl') = getWatched wl l in
  addWatches (write wl' (litIndex l) (c::clauses)) rest

Assignments : Type
Assignments = LinArray (Maybe Bool)

varIndex : Var -> Int
varIndex (MkVar n) = n

value : (1 _ : Assignments) -> Var -> LPair (Maybe Bool) (Assignments)
value as var = let (v # as') = mread as (varIndex var) in
                   case v of
                        Just x => (x # as')
                        Nothing => (Nothing # as')

assign : (1 _ : Assignments) -> Var -> Bool -> Assignments
assign as var v = write as (varIndex var) (Just v)

unassign : (1 _ : Assignments) -> Var -> Assignments
unassign as var = write as (varIndex var) Nothing

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

updateWatchlist : (1 _ : Watchlist) -> Lit -> (1 _ : Assignments) -> LPair Bool (Watchlist, Assignments)
updateWatchlist wl assignFalse as =
  let (clauses # wl) = getWatched wl assignFalse in
      case clauses of
           [] => True # (wl, as)
           (c::rest) =>
               let (alts # as') = lfoldra findAlt (Just [] # as) (c::rest) in
                   case alts of
                        Nothing => False # (wl, as')
                        Just alts => let wl' = removeWatches wl assignFalse
                                         wl'' = addWatches wl' alts
                                     in True # (wl'', as')
      where
  altOk : List Lit -> (1 _ : Assignments) -> LPair (Maybe Lit) Assignments
  altOk [] as = (Nothing # as)
  altOk (l::ls) as =
    case value as (getVar l) of
         ((Just x) # as') => if x == isPos l then (Just l) # as'
                                             else altOk ls as'
         ((Nothing) # as') => (Just l) # as'

  findAlt : (1 _ : Clause) -> (1 _ : LPair (Maybe (List (Lit, Clause))) Assignments) -> LPair (Maybe (List (Lit, Clause))) Assignments
  findAlt (MkClause ls) (acc # as) = let (mlit # as') = altOk ls as in
                                         case mlit of
                                              Just l => (map ((::) (l, MkClause ls)) acc # as')
                                              Nothing => (Nothing # as')

mutual
  solveTry : Bool -> Int -> Int -> (1 _ : Watchlist) -> (1 _ : Assignments) -> LPair Bool (Watchlist, Assignments)
  solveTry a numVars d wl as =
    let as' = assign as (MkVar d) a
        (ok # (wl', as'')) = updateWatchlist wl (if a then MkNeg (MkVar d) else MkPos (MkVar d)) as'
        in
        if ok then True # (wl', as'')
              else False # (wl', unassign as'' (MkVar d))

  solve : Int -> Int -> (1 _ : Watchlist) -> (1 _ : Assignments) -> LPair Bool (Watchlist, Assignments)
  solve numVars d wl as = if d >= numVars then True # (wl, as) else
    case (solveTry False numVars d wl as) of
         (True # (wl', as')) => case (solve numVars (assert_smaller d (d+1)) wl' as') of
                                     (False # (wl'', as'')) => trytrue numVars d wl'' (unassign as'' (MkVar d))
                                     r => r
         (False # (wl', as')) => trytrue numVars d wl' as'
         where
           trytrue : Int -> Int -> (1 _ : Watchlist) -> (1 _ : Assignments) -> LPair Bool (Watchlist, Assignments)
           trytrue numVars d wl as = case (solveTry True numVars d wl as) of
                                                  (True # (wl', as')) => solve numVars (assert_smaller d (d+1)) wl' as'
                                                  f => f

export
sat : Int -> List Clause -> Maybe (List (Var, Bool))
sat numVars clauses =
  let wl = initWatchlist (2 * numVars) clauses
      as = initAssignments numVars
      (r # (wl', as')) = solve numVars 0 wl as in
      if r then traverse result (dumpArr as')
           else Nothing
  where
    result : (Var, Maybe Bool) -> Maybe (Var, Bool)
    result (v, Just a) = Just (v, a)
    result (_, Nothing) = Nothing
