{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Interpreter.ShowPT where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.ModSwPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT

unSPT :: ShowPT d a -> String
unSPT (SPT a) = a 0

newtype ShowPT (d :: Depth) a = SPT {unSPT' :: Int -> String}

lift2 :: (Applicative i) => ((Int -> String) -> (Int -> String) -> (Int -> String)) -> i (ShowPT d a) -> i (ShowPT d' b) -> i (ShowPT d'' c)
lift2 f a b = SPT <$> (f <$> (unSPT' <$> a) <*> (unSPT' <$> b))

instance AddPT (ShowPT) where
  type AddPubCtxPT   i ShowPT d a = (Show a, Functor i)
  type MulPubCtxPT   i ShowPT d a = (Show a, Functor i)
  type AdditiveCtxPT i ShowPT d a = (Applicative i)

  (+#) = lift2 $ \a b i -> "( " ++ a i ++ " )" ++ " + " ++ "( " ++ b i ++ " )"
  negPT = fmap $ \a -> SPT $ \i -> "neg $ " ++ unSPT' a i
  addPublicPT a = fmap $ \b -> SPT $ \i -> "( " ++ (show a) ++ " )" ++ " + " ++ "( " ++ unSPT' b i ++ " )"
  mulPublicPT a = fmap $ \b -> SPT $ \i -> "( " ++ (show a) ++ " )" ++ " * " ++ "( " ++ unSPT' b i ++ " )"

instance MulPT ShowPT where

  type RingCtxPT i ShowPT d a = (Applicative i)

  (*#) = lift2 $ \a b i -> "( " ++ a i ++ " )" ++ " * " ++ "( " ++ b i ++ " )"
{-
instance ModSwPT ShowPT where

  type ModSwitchCtxPT ShowPT d a zp' = ()

  modSwitchDec (SPT a) = SPT $ \i -> "modSwitchDec $ " ++ a i

instance (Applicative mon) => TunnelPT mon ShowPT where

  type TunnelCtxPT ShowPT d t e r s zp = ()

  tunnelPT _ = pure $ \(SPT a) -> SPT $ \i -> "tunnel <FUNC> $ " ++ a i
-}

instance LambdaD ShowPT where
  lamD f = fmap showF $ J $ fmap unJ $ unJ $ f $ J $ pure id
    where showF g = SPT $ \i ->
            let x = "x" ++ show i
                (SPT b) = g $ SPT $ const x
            in "\\" ++ x ++ " -> " ++ (b $ i+1)

  appD mf ma = (\(SPT f) (SPT a) -> SPT $ \i -> "( " ++ f i ++ " ) " ++ a i) <$> mf <*> ma

instance Lit (ShowPT d) where
  type LitCtx (ShowPT d) a = (Show a)
  lit a = SPT $ \_ -> show a
