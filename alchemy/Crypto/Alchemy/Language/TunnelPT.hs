
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.TunnelPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc, Factored, Linear)
import GHC.Exts

-- | Symantics for leveled plaintext operations of some depth @d@.

class (Applicative mon) => TunnelPT mon expr where

  type TunnelCtxPT expr (d :: Depth) (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  tunnelPT :: (TunnelCtxPT expr d t e r s zp)
           => Linear t zp e r s -> mon (expr (h :: [*]) d (Cyc t r zp) -> expr h d (Cyc t s zp))


{-
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Crypto.Alchemy.Language.TunnelPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc, Factored, Linear)
import Data.Singletons.Prelude.List
import GHC.Exts

-- | Symantics for leveled plaintext operations of some depth @d@.

class TunnelPT expr where

  type TunnelCtxPT expr (d :: Depth) (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint
  type TunnHintType expr (d :: Depth) (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp

  tunnelPT :: (TunnelCtxPT expr d t e r s zp)
           => Linear t zp e r s -> expr h d (Cyc t r zp) -> expr (h :++ '[TunnHintType expr d t e r s zp]) d (Cyc t s zp)
-}