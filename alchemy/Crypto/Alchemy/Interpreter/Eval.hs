{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Crypto.Alchemy.Interpreter.Eval ( E, eval ) where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Coerce
import Data.Tuple

import Algebra.Additive as Additive
import Algebra.Ring     as Ring

import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.Pair
import Crypto.Alchemy.Language.SHE
import Crypto.Alchemy.Language.String

import Crypto.Lol                      hiding (String)
import Crypto.Lol.Applications.SymmSHE as SHE
import Crypto.Lol.Types

-- | Metacircular evaluator.
newtype E e a = E { unE :: e -> a }
  deriving (Functor, Applicative)

-- | Evaluate a closed expression (i.e., one having no unbound
-- variables)
eval :: E () a -> a
eval = flip unE ()

instance Lambda E where
  newtype Arrow E a b = EA { unEA :: (a -> b) } deriving (Functor, Applicative)
  lam    = coerce . curry . unE
  f $: a = coerce f <*> a
  v0     = E   snd
  s a    = E $ unE a . fst

arrow1 :: (a -> b) -> Arrow E a b
arrow1 = coerce

arrow2 :: (a -> b -> c) -> Arrow E a (Arrow E b c)
arrow2 = coerce

pureE1 :: (a -> b) -> E e (Arrow E a b)
pureE1 = pure . arrow1

pureE2 :: (a -> b -> c) -> E e (Arrow E a (Arrow E b c))
pureE2 = pure . arrow2

instance Additive.C a => Add E a where
  add_ = pureE2 (+)
  neg_ = pureE1 negate

instance Additive.C a => AddLit E a where
  addLit_ x = pureE1 (x +)

instance Ring.C a => Mul E a where
  type PreMul E a = a
  mul_ = pureE2 (*)

instance Ring.C a => MulLit E a where
  mulLit_ x = pureE1 (x *)

instance (RescaleCyc (Cyc t) (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i),
          Fact m)
  => Div2 E (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2 E (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) =
    Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i)
  -- since input is divisible by two, it doesn't matter which basis we use
  div2_ = pureE1 rescalePow

instance (RescaleCyc (Cyc t) (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i),
          Fact m)
  => Div2 E (PNoiseTag h (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) where
  type PreDiv2 E (PNoiseTag h (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) =
    PNoiseTag h (Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i))
  -- since input is divisible by two, it doesn't matter which basis we use
  div2_ = pureE1 $ PTag . rescalePow . unPTag

instance (RescaleCyc (Cyc t) (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i),
          Fact m)
  => Div2 E (Identity (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) where
  type PreDiv2 E (Identity (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) =
    Identity (Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i))
  -- since input is divisible by two, it doesn't matter which basis we use
  div2_ = pureE1 $ Identity . rescalePow . runIdentity

instance (SHE.ModSwitchPTCtx t m' (ZqBasic ('PP '(Prime2, 'S k)) i) (ZqBasic ('PP '(Prime2, k)) i) zq) =>
  Div2 E (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) where
  type PreDiv2 E (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) =
    CT m (ZqBasic ('PP '(Prime2, 'S k)) i) (Cyc t m' zq)

  div2_ = pureE1 modSwitchPT

instance List E where
  nil_  = pure []
  cons_ = pureE2 (:)

coerceFmap :: forall f a b . (Functor f) => Arrow E (Arrow E a b) (Arrow E (f a) (f b))
coerceFmap = coerce (fmap :: (a -> b) -> f a -> f b)

instance Functor_ E where
  -- can't use arrow2 here
  fmap_ = pure $ EA $ (\f -> EA $ \as -> fmap (unEA f) as)

instance Applicative_ E where
  pure_ = pureE1 pure
  ap_   = pure $ EA $ (\f -> EA $ \a -> (unEA <$> f) <*> a) --arrow2 (<*>)

instance Monad_ E where
  bind_ = pureE (>>=)

instance MonadReader_ E where
  ask_   = pure ask
  local_ = pureE1 local

instance MonadWriter_ E where
  tell_   = pureE1 tell
  listen_ = pureE1 listen

instance SHE E where

  type ModSwitchPTCtx   E (CT m zp (Cyc t m' zq)) zp' = (SHE.ModSwitchPTCtx t m' zp zp' zq)
  type ModSwitchCtx     E (CT m zp (Cyc t m' zq)) zq' = (RescaleCyc (Cyc t) zq zq', ToSDCtx t m' zp zq)
  type AddPublicCtx     E (CT m zp (Cyc t m' zq))     = (SHE.AddPublicCtx t m m' zp zq)
  type MulPublicCtx     E (CT m zp (Cyc t m' zq))     = (SHE.MulPublicCtx t m m' zp zq)
  type KeySwitchQuadCtx E (CT m zp (Cyc t m' zq)) gad = (SHE.KeySwitchCtx gad t m' zp zq)
  type TunnelCtx        E t e r s e' r' s' zp zq gad  = (SHE.TunnelCtx t r s e' r' s' zp zq gad)

  modSwitchPT_     = pureE1 modSwitchPT
  modSwitch_       = pureE1 modSwitch
  addPublic_       = pureE1 . addPublic
  mulPublic_       = pureE1 . mulPublic
  keySwitchQuad_   = pureE1 . keySwitchQuadCirc
  tunnel_          = pureE1 . SHE.tunnel

instance (Applicative rep) => LinearCyc E rep where
  type PreLinearCyc E rep = rep
  type LinearCycCtx E rep t e r s zp = (e `Divides` r, e `Divides` s, CElt t zp)

  linearCyc_ f = pureE1 $ fmap (evalLin f)

-- | Uses 'SHE.errorTermUnrestricted' to compute 'errorRate'.
instance ErrorRate E where
  type ErrorRateCtx E (CT m zp (Cyc t m' zq)) z =
    (SHE.ErrorTermUCtx t m' z zp zq, Mod zq, ToInteger (LiftOf zq))

  errorRate_ :: forall t m' m z zp zq ct e .
                (ErrorRateCtx E ct z, ct ~ CT m zp (Cyc t m' zq)) =>
                SHE.SK (Cyc t m' z) -> E e (Arrow E ct Double)
  errorRate_ sk = pureE1 $
    (/ (fromIntegral $ proxy modulus (Proxy::Proxy zq))) .
    fromIntegral . maximum . fmap abs . SHE.errorTermUnrestricted sk

instance String E where
  string_ = pure

instance Pair E where
  pair_ = pureE2 (,)
