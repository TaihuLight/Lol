{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE TypeFamilies        #-}

module Crypto.Alchemy.Interpreter.ShowIR where

import Algebra.Additive as Additive (C(..))
import Algebra.Ring as Ring (C)

import Control.Monad.Identity

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.IR
import Crypto.Lol

data ShowIR (a :: *) = SIR {bindID::Int, unSIR::String}

instance Lambda ShowIR where
  lam f =
    -- EAC: use laziness!
    let (SIR i b) = f $ SIR i ("x" ++ show i)
    in SIR (i+1) $ "\\x" ++ show i ++ " -> " ++ b
  app (SIR i f) (SIR _ a) = SIR i $ "( " ++ f ++ " ) " ++ a

instance (Monad mon) => SymIR mon ShowIR where

  type RescaleCtxIR   ShowIR t m m' zp zq' zq = ()
  type AddPubCtxIR    ShowIR t m m' zp     zq = (Show (Cyc t m zp))
  type MulPubCtxIR    ShowIR t m m' zp     zq = (Show (Cyc t m zp))
  type KeySwitchCtxIR ShowIR t m m' zp     zq = ()
  type TunnelCtxIR    ShowIR t e r s r' s' zp zq = ()

  rescaleIR = return $ \(SIR _ a) -> SIR 0 $ "rescale $ " ++ a
  addPublicIR = return $ \a (SIR _ b) -> SIR 0 $ "( " ++ show a ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  mulPublicIR = return $ \a (SIR _ b) -> SIR 0 $ "( " ++ show a ++ " )" ++ " * " ++ "( " ++ b ++ " )"
  keySwitchQuadIR = return $ \(SIR _ a) -> SIR 0 $ "keySwitch $ " ++ a
  tunnelIR _ = return $ \(SIR _ a) -> SIR 0 $ "tunnel <FUNC> $ " ++ a

instance Additive.C (ShowIR a) where
  zero = SIR 0 "0"
  (SIR _ a) + (SIR _ b) = SIR 0 $ "( " ++ a ++ " )" ++ " + " ++ "( " ++ b ++ " )"
  negate (SIR _ a) = SIR 0 $ "neg $ " ++ a

instance Ring.C (ShowIR a) where
  one = SIR 0 "1"
  (SIR _ a) * (SIR _ b)  = SIR 0 $ "( " ++ a ++ " )" ++ " * " ++ "( " ++ b ++ " )"

instance Lit ShowIR where
  type LitCtx ShowIR a = (Show a)
  lit a = SIR 0 $ show a
