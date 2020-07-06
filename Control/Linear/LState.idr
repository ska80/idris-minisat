module Control.Linear.LState

import Control.Linear

%default total

export
data LState : (stateType : Type) -> (a : Type) -> Type where
  MkLState : (1 f : ((1 _ : stateType) -> (LPair a stateType))) -> LState stateType a

export
Functor (LState stateType) where
  map f (MkLState c) = MkLState (\s => let (r # s') = c s in ((f r) # s'))

export
Applicative (LState stateType) where
  pure x = MkLState (\s => x # s)
  (MkLState cf) <*> (MkLState cv) = MkLState (\s =>
                                    let (f # s') = cf s
                                        (r # s'') = cv s'
                                        in ((f r) # s''))

export
LMonad (LState s) where
  (>>=) (MkLState f) c = MkLState (\x => let (res # s') = f x in
                                                 let (MkLState r2) = c res
                                                      in r2 s')

export
pure : (val : a) -> LState s a
pure val = MkLState (\s => (val # s))

export
run : (f : (1 state : s) -> (LPair a s)) -> LState s a
run f = MkLState f

export
change : (f : (1 state : s) -> s) -> LState s ()
change f = MkLState (\state => (() # f state))

public export
interface SubState a b where
  liftSt : LState a r -> LState b r

export
SubState a (a, b) where
  liftSt (MkLState f) = MkLState (\(sa, sb) => let (res # sa') = f sa in
                                                  (res # (sa', sb)))

export
SubState a (b, a) where
  liftSt (MkLState f) = MkLState (\(sb, sa) => let (res # sa') = f sa in
                                                  (res # (sb, sa')))

export
runLState : (1 initState : stateType) -> (1 c : LState stateType r) -> LPair r stateType
runLState s (MkLState f) = f s

export
execLState : (1 initState : stateType) -> (1 c : LState stateType r) -> stateType
execLState s (MkLState f) = let (_ # finState) = f s in finState
