
module Crypto.Alchemy.Language.Monad where

import Crypto.Alchemy.Language.Lambda

import Control.Monad.Reader
import Control.Monad.Writer

-- | Symantics for functors: promotes any 'Functor' to the object
-- language. (Instances should obey the monad laws.)

class Lambda expr => Functor_ expr where
  -- | Object-language analogue of 'fmap'.
  fmap_ :: (Functor f) => expr e (Arrow expr
                                   (Arrow expr a b)
                                   (Arrow expr (f a) (f b)))

-- | Convenient metalanguage version of 'fmap_'.
infixl 4 <$:>
(<$:>) :: (Functor_ expr, Functor f) =>
          expr e (Arrow expr a b) -> expr e (f a) -> expr e (f b)
f <$:> a = fmap_ $: f $: a

-- | Symantics for applicative monads: promotes any 'Applicative' to
-- the object language. (Instances should obey the monad laws.)

class (Functor_ expr) => Applicative_ expr where
  -- | Object-language analogue of 'pure'.
  pure_ :: (Applicative f) => expr e (Arrow expr a (f a))

  -- | Object-language analogue of '(<*>)'.
  ap_   :: (Applicative f) => expr e (Arrow expr (f (Arrow expr a b))
                                      (Arrow expr (f a) (f b)))

-- | Convenient metalanguage version of 'ap_'.
infixl 4 <*:>
(<*:>) :: (Applicative_ expr, Applicative f) =>
  expr e (f (Arrow expr a b)) -> expr e (f a) -> expr e (f b)
f <*:> a = ap_ $: f $: a

-- | Object-language analogue of 'liftA' (synonym for 'fmap_').
liftA_ :: (Applicative_ expr, Applicative f) =>
          expr e (Arrow expr (Arrow expr a b) (Arrow expr (f a) (f b)))
liftA_ = fmap_

-- | Object-language analogue of 'liftA2' (synonym for 'fmap_').
liftA2_ :: (Applicative_ expr, Applicative f) =>
           expr e (Arrow expr (Arrow expr a (Arrow expr b c))
                    (Arrow expr (f a) (Arrow expr (f b) (f c))))
-- everything must be written in the object language here because
-- that's where liftA2_ lives
liftA2_ = lam $ lam $ lam $ ap_ $: (fmap_ $: v2 $: v1) $: v0

-- | Symantics for monads: promotes any 'Monad' to the object
-- language. (Instances should obey the monad laws.)

class (Applicative_ expr) => Monad_ expr where
  -- | Object-language analogue of '(>>=)'.
  bind_ :: (Monad m) => expr e (Arrow expr (m a)
                                 (Arrow expr (Arrow expr a (m b)) (m b)))

-- | Convenient metalanguage version of 'bind_'.
infixl 1 >>=:
(>>=:) :: (Monad_ expr, Monad m) =>
          expr e (m a) -> expr e (Arrow expr a (m b)) -> expr e (m b)
a >>=: f = bind_ $: a $: f

return_ :: (Monad_ expr, Monad m) => expr e (Arrow expr a (m a))
return_ = pure_

-- | Symantics for reader monads: promotes any 'MonadReader' to the
-- object language.

class (Monad_ expr) => MonadReader_ expr where
  -- | Object-language analogue of 'ask'.
  ask_   :: (MonadReader r m) => expr e (m r)

  -- | Object-language analogue of 'local'.
  local_ :: (MonadReader r m) =>
    expr e (Arrow expr (Arrow expr r r) (Arrow expr (m a) (m a)))

-- | Symantics for writer monads: promotes any 'MonadWriter' to the
-- object language.

class (Monad_ expr) => MonadWriter_ expr where
  -- | Object-language analogue of 'tell'.
  tell_   :: (MonadWriter w m) => expr e (Arrow expr w (m ()))

  -- | Object-language analogue of 'listen_'.
  listen_ :: (MonadWriter w m) => expr e (Arrow expr (m a) (m (a,w)))
