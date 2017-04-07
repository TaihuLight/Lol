{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Crypto.Alchemy.Language.AddPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc)
import Data.Singletons.Prelude.List
import GHC.Exts (Constraint)

infixl 6  +#, -#

-- | Symantics for leveled plaintext operations of some depth @d@.

class AddPT expr where
  type AddPubCtxPT   expr (d :: Depth) a :: Constraint
  type MulPubCtxPT   expr (d :: Depth) a :: Constraint
  type AdditiveCtxPT expr (d :: Depth) a :: Constraint

  addPublicPT :: (AddPubCtxPT expr d a, a ~ Cyc t m zp) => a -> expr h d a -> expr h d a

  mulPublicPT :: (MulPubCtxPT expr d a, a ~ Cyc t m zp) => a -> expr h d a -> expr h d a

  (+#) :: (AdditiveCtxPT expr d a, a ~ Cyc t m zp) => expr (h1 :: [*]) d a -> expr (h2 :: [*]) d a -> expr (h1 :++ h2) d a

  negPT :: (AdditiveCtxPT expr d a, a ~ Cyc t m zp) => expr h d a -> expr h d a

(-#) :: (AddPT expr, AdditiveCtxPT expr d a, a ~ Cyc t m zp)
     => expr (h1 :: [*]) d a -> expr (h2 :: [*]) d a -> expr (h1 :++ h2) d a
a -# b = a +# (negPT b)

{-
convert :: (a -> Reader m b) -> Reader m (a -> b)
convert f = do
  m <- ask
  return $ \a -> flip runReader m $ f a
-}