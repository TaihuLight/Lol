{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Crypto.Alchemy.Language.Wrap (Wrap, unwrap, encryptArg, injectCyc, liftW2) where

import Crypto.Alchemy.Interpreter.Compiler.Environment

import Crypto.Lol
import Crypto.Lol.Applications.SymmSHE

import Control.Monad.Random
import Control.Monad.State
import Data.Typeable

newtype Wrap a = W {unwrap :: a} deriving (Functor, Show)

injectCyc :: Cyc t m r -> Wrap (Cyc t m r)
injectCyc = W

encryptArg :: forall t m m' z zp zq rnd .
  (EncryptCtx t m m' z zp zq, z ~ LiftOf zp, Typeable t, Typeable m', Typeable z, MonadRandom rnd)
  => P2CState -> Cyc t m zp -> Maybe (rnd (Wrap (CT m zp (Cyc t m' zq))))
encryptArg st x = flip evalState st $ do
  (sk :: Maybe (SK (Cyc t m' z))) <- lookupKey -- ONLY lookup the key, do NOT generate!
  return $ (\s -> W <$> encrypt s x) <$> sk

liftW2 :: (a -> b -> c) -> Wrap a -> Wrap b -> Wrap c
liftW2 f (W a) (W b) = W $ f a b