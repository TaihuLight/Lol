
module Crypto.Alchemy.Language.Monad where

import Crypto.Alchemy.Language.Lambda

import Control.Monad.Reader
import Control.Monad.Writer

-- | Symantics for functors: promotes any 'Functor' to the object
-- language. (Instances should obey the monad laws.)

class Lambda expr => Functor_ expr where
  -- | Object-language analogue of 'fmap'.
  fmap_ :: (Functor f) => 
    expr e (Arrow expr a b) -> expr e (f a) -> expr e (f b)

-- | Synonym for 'fmap_'.
infixl 4 <$:>
(<$:>) :: (Functor_ expr, Functor f) =>
  expr e (Arrow expr a b) -> expr e (f a) -> expr e (f b)
(<$:>) = fmap_

-- | Symantics for applicative monads: promotes any 'Applicative' to
-- the object language. (Instances should obey the monad laws.)

class (Functor_ expr) => Applicative_ expr where
  -- | Object-language analogue of 'pure'.
  pure_ :: (Applicative f) => expr e a -> expr e (f a)

  -- | Object-language analogue of '(<*>)'.
  infixl 4 <*:>
  (<*:>) :: (Applicative f) => 
    expr e (f (Arrow expr a b)) -> expr e (f a) -> expr e (f b)

-- | Object-language analogue of 'liftA' (synonym for 'fmap_').
liftA_ :: (Applicative_ expr, Applicative f) => 
  expr e (Arrow expr a b) -> expr e (f a) -> expr e (f b)
liftA_ = fmap_

-- | Object-language analogue of 'liftA2'.
liftA2_ :: (Applicative_ expr, Applicative f) =>
  expr e (Arrow expr a (Arrow expr b c)) ->
  expr e (f a) -> expr e (f b) -> expr e (f c)
liftA2_ f a b = liftA_ f a <*:> b

-- | Object-language analogue of 'liftA3'.
liftA3_ :: (Applicative_ expr, Applicative f) =>
  expr e (Arrow expr a (Arrow expr b (Arrow expr c d))) ->
  expr e (f a) -> expr e (f b) -> expr e (f c) -> expr e (f d)
liftA3_ f a b c = liftA2_ f a b <*:> c

-- | Symantics for monads: promotes any 'Monad' to the object
-- language. (Instances should obey the monad laws.)

class (Applicative_ expr) => Monad_ expr where
  -- | Object-language analogue of '(>>=)'.
  infixl 1 >>=:
  (>>=:) :: (Monad m) => 
    expr e (m a) -> expr e (Arrow expr a (m b)) -> expr e (m b)

return_ :: (Monad_ expr, Monad m) => expr e a -> expr e (m a)
return_ = pure_

-- | Symantics for reader monads: promotes any 'MonadReader' to the
-- object language.

class (Monad_ expr) => MonadReader_ expr where
  -- | Object-language analogue of 'ask'.
  ask_   :: (MonadReader r m) => expr e (m r)

  -- | Object-language analogue of 'local'.
  local_ :: (MonadReader r m) => 
    expr e (Arrow expr r r) -> expr e (m a) -> expe e (m a)

-- | Symantics for writer monads: promotes any 'MonadWriter' to the
-- object language.

class (Monad_ expr) => MonadWriter_ expr where
  -- | Object-language analogue of 'tell'.
  tell_   :: (MonadWriter w m) => expr e w -> expr e (m ())

  -- | Object-language analogue of 'listen_'.
  listen_ :: (MonadWriter w m) => expr e (m a) -> expr e (m (a,w))
