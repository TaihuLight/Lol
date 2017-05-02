{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.NoiseWriter
( NoiseWriter, writeNoise )
where

import Control.Monad.Writer.Class

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.Monad

-- CJP: also need some structure to give us secret keys
-- | A transformer that additionally logs the sizes of the noise terms
-- of any ciphertexts created during interpretation.
newtype NoiseWriter expr m e a =
  NW { unNW :: expr (Monadify m e) (Monadify m a) }

type family Monadify m a where
  Monadify m (a,b) = (Monadify m a, Monadify m b)
  Monadify m (a -> b) = Monadify m a -> Monadify m b
  Monadify m a = m a

-- CJP: should String be replaced by something more structured?  E.g.,
-- Integer to carry the largest noise coeff?  Or Double to carry the
-- noise rate?
type NoiseLog = [String]

writeNoise :: NoiseWriter expr m e a -> expr (Monadify m e) (Monadify m a)
writeNoise = unNW

instance (Lambda expr) => Lambda (NoiseWriter expr m) where
  lam    = NW . lam . unNW
  f $: a = NW $ unNW f $: unNW a
  v0     = NW v0
  s      = NW . s . unNW


-- | Log the noise rate of a given ciphertext.
tellNoiseRate :: forall t m' m z zp zq mon ct .
  (ErrorTermUCtx t m' z zp zq, Mod zq, ToInteger (LiftOf zq),
   MonadWriter NoiseLog mon, ct ~ CT m zp (Cyc t m' zq)) =>
  SK (Cyc t m' z) -> ct -> mon ct
tellNoiseRate sk =
  let noiseRate =
        (/ (fromIntegral $ proxy modulus (Proxy::Proxy zq))) .
        fromIntegral . maximum . fmap abs . errorTermUnrestricted sk
  in \ct -> do
    tell [show (noiseRate ct :: Double) ++ "\n"]
    return ct

instance (MonadWriter NoiseLog mon, ct ~ (CT m zp (Cyc t m zq)),
          Applicative_ expr, Add expr ct {- CJP: more for extracting error -})
         => Add (NoiseWriter expr mon) ct where

  add_ = NW $ liftA2_ $: add_

  neg_ = NW $ liftA_ $: neg_  -- don't log error because it doesn't grow
