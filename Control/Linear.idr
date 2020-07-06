module Control.Linear

%default total

public export
interface Applicative m => LMonad m where
  (>>=) : (1 _ : m a) -> (1 f : ((_ : a) -> m b)) -> m b

export
lfoldlM : (Foldable t, LMonad m) => (funcM: a -> b -> m a) -> (init: a) -> (input: t b) -> m a
lfoldlM fm a0 = foldl (\ma,b => ma >>= flip fm b) (pure a0)
