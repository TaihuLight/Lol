{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Crypto.Alchemy.Language.MulPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc, Proxy, LiftOf)
import Data.Singletons.Prelude.List
import GHC.Exts

infixl 7 *#

-- | Symantics for leveled plaintext operations of some depth @d@.

class MulPT expr where

  type RingCtxPT expr (d :: Depth) a :: Constraint
  type KSHintType expr (d :: Depth) a

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').
  (*#) :: (RingCtxPT expr d a, a ~ Cyc t m zp) =>
          -- CJP: generalize input depths?
          expr h1 (Add1 d) a -> expr h2 (Add1 d) a -> expr (h1 :++ h2 :++ '[(Proxy (LiftOf zp), KSHintType expr d a)]) d a