{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Interpreter.Print
( P, pprint
)
where

import Crypto.Alchemy.Interpreter.PT2CT.Noise
import Crypto.Alchemy.Language.Arithmetic
import Crypto.Alchemy.Language.Lambda
import Crypto.Alchemy.Language.LinearCyc
import Crypto.Alchemy.Language.List
import Crypto.Alchemy.Language.Monad
import Crypto.Alchemy.Language.SHE

import Crypto.Lol                      (Cyc, Pos (..), Prime2,
                                        PrimePower (..))
import Crypto.Lol.Applications.SymmSHE (CT)
import Crypto.Lol.Types

import Control.Monad.Identity

-- the Int is the nesting depth of lambdas outside the expression
newtype P e a = P { unP :: Int -> String }

-- | Pretty-print a closed expression.
pprint :: P () a -> String
pprint = flip unP 0

pprint1  :: String -> P e a           -> P e b
pprint2  :: String -> P e a  -> P e b -> P e c
pprint2' :: String -> String -> P e a -> P e b
pprintIn :: String -> P e a  -> P e b -> P e c

pprint1  op a   = P $ \i -> "(" ++ op ++ " " ++ unP a i ++ ")"
pprint2  op a b = P $ \i -> "(" ++ op ++ " " ++ unP a i ++ " " ++ unP b i ++ ")"
pprint2' op a b = P $ \i -> "(" ++ op ++ " " ++ a       ++ " " ++ unP b i ++ ")"
pprintIn op a b = P $ \i -> "(" ++ unP a i ++ " " ++ op ++ " " ++ unP b i ++ ")"

-- | In the printout, variable indices grow "outside in," rather than
-- "inside out" (as in object-language code) because the
-- implementation is simpler that way.

instance Lambda P where
  data Arrow P a b              -- unused, so empty type
  lam f = P $ \i -> "(\\v" ++ show  i ++ " -> " ++ unP f (i+1) ++ ")"
  ($:)  = pprintIn ""
  v0    = P $ \i -> "v" ++ show (i-1)
  s  v  = P $ \i -> unP v (i-1)

instance List P where
  nil_  = P $ const "nil"
  cons_ = pprint2 "cons"

instance Add P a where
  (+:) = pprintIn "+"
  neg_ = pprint1  "neg"

instance Show a => AddLit P a where
  (>+:) a = pprint2' ">+" (show a)

instance Mul P a where
  type PreMul P a = a
  (*:) = pprintIn "*"

instance Show a => MulLit P a where
  (>*:) a = pprint2' "mulLit" (show a)

instance Div2 P (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) where
  type PreDiv2 P (Cyc t m (ZqBasic ('PP '(Prime2, k)) i)) =
    Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i)
  div2_ = pprint1 "div2"

instance Div2 P (PNoiseTag h (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) where
  type PreDiv2 P (PNoiseTag h (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) =
    PNoiseTag h (Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i))
  div2_ = pprint1 "div2"

instance Div2 P (Identity (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) where
  type PreDiv2 P (Identity (Cyc t m (ZqBasic ('PP '(Prime2, k)) i))) =
    Identity (Cyc t m (ZqBasic ('PP '(Prime2, 'S k)) i))
  div2_ = pprint1 "div2"

instance Div2 P (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) where
  type PreDiv2 P (CT m (ZqBasic ('PP '(Prime2, k)) i) (Cyc t m' zq)) =
    CT m (ZqBasic ('PP '(Prime2, 'S k)) i) (Cyc t m' zq)
  div2_ = pprint1 "div2"

instance Functor_ P where
  fmap_ = pprint2 "fmap"

instance Applicative_ P where
  pure_  = pprint1  "pure"
  (<*:>) = pprintIn "<*>"

instance Monad_ P where
  (>>=:) = pprintIn ">>="

instance MonadReader_ P where
  ask_   = P $ const "ask"
  local_ = pprint2 "local"

instance MonadWriter_ P where
  tell_   = pprint1 "tell"
  listen_ = pprint1 "listen"

instance LinearCyc P rep where
  type PreLinearCyc P rep = rep
  type LinearCycCtx P rep t e r s zp = ()

  linearCyc_ _ = pprint1 "linearCyc <FUNC>"

instance SHE P where

  type ModSwitchPTCtx   P a zp' = ()
  type ModSwitchCtx     P a zq' = ()
  type AddPublicCtx     P (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type MulPublicCtx     P (CT m zp (Cyc t m' zq)) = (Show (Cyc t m zp))
  type KeySwitchQuadCtx P a gad = ()
  type TunnelCtx        P t e r s e' r' s' zp zq gad = ()

  modSwitchPT_     = pprint1  "modSwitchPT"
  modSwitch_       = pprint1  "modSwitch"
  addPublic_     p = pprint2' "addPublic" (show p)
  mulPublic_     p = pprint2' "mulPublic" (show p)
  keySwitchQuad_ _ = pprint1  "keySwitchQuad <HINT>"
  tunnel_        _ = pprint1  "tunnel <HINT>"

instance ErrorRate P where
  type ErrorRateCtx P ct z = ()
  errorRate_ _ = pprint1 "errorRate"

