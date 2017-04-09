{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs, MultiParamTypeClasses, RankNTypes, TypeFamilies, TypeOperators #-}

module Crypto.Alchemy.Interpreter.Duplicate where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.CT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT


import Data.Constraint           hiding ((***), (&&&))
import Data.Singletons.Prelude.List ((:++))
import Unsafe.Coerce

duplicate :: Dup expr1 expr2 a -> (expr1 a, expr2 a)
duplicate (Dup a b) = (a,b)

dupPT ::  DupPT expr1 expr2 h d a -> (expr1 (Fsts h) d a, expr2 (Snds h) d a)
dupPT (DupPT a b) = (a,b)

data Dup expr1 expr2 a = Dup {unDupA :: expr1 a, unDupB :: expr2 a}

data DupPT expr1 expr2 (h :: [*]) (d :: Depth) a where
  DupPT :: {unDupPTA :: expr1 (Fsts hs) d a, unDupPTB :: expr2 (Snds hs) d a} -> DupPT expr1 expr2 hs d a


appFsts :: forall f h1 h2 (d :: Depth) a . f h1 d a -> f h2 d a -> (() :- ((Fsts (h1 :++ h2)) ~ ((Fsts h1) :++ (Fsts h2))))
appFsts _ _ = Sub $ unsafeCoerce (Dict :: Dict ())

appSnds :: forall f h1 h2 (d :: Depth) a . f h1 d a -> f h2 d a -> (() :- ((Snds (h1 :++ h2)) ~ ((Snds h1) :++ (Snds h2))))
appSnds _ _ = Sub $ unsafeCoerce (Dict :: Dict ())

instance (AddPT expr1, AddPT expr2) => AddPT (DupPT expr1 expr2) where
  type AddPubCtxPT    (DupPT expr1 expr2) d a =
    (AddPubCtxPT expr1 d a, AddPubCtxPT expr2 d a)
  type MulPubCtxPT    (DupPT expr1 expr2) d a =
    (MulPubCtxPT expr1 d a, MulPubCtxPT expr2 d a)
  type AdditiveCtxPT  (DupPT expr1 expr2) d a =
    (AdditiveCtxPT expr1 d a, AdditiveCtxPT expr2 d a)

  addPublicPT a (DupPT b c) = DupPT (addPublicPT a b) (addPublicPT a c)
  mulPublicPT a (DupPT b c) = DupPT (mulPublicPT a b) (mulPublicPT a c)

  a@(DupPT a1 a2) +# b@(DupPT b1 b2) = (DupPT (a1 +# b1) (a2 +# b2)) \\ appFsts a b \\ appSnds a b

  negPT (DupPT a b) = DupPT (negPT a) (negPT b)

instance (MulPT expr1, MulPT expr2) => MulPT (DupPT expr1 expr2) where
  type RingCtxPT (DupPT expr1 expr2) d a = (RingCtxPT expr1 d a, RingCtxPT expr2 d a)
  type KSHintType (DupPT expr1 expr2) d a = (KSHintType expr1 d a, KSHintType expr2 d a)


  --(*#) :: (RingCtxPT expr d a, a ~ Cyc t m zp) =>
          -- CJP: generalize input depths?
  --        expr h1 (Add1 d) a -> expr h2 (Add1 d) a -> expr (h1 :++ h2 :++ '[KSHintType expr d a]) d a
  a@(DupPT a1 a2) *# b@(DupPT b1 b2) = (DupPT (a1 *# b1) (a2 *# b2)) \\ appFsts a b \\ appSnds a b

instance (Lit expr1, Lit expr2) => Lit (Dup expr1 expr2) where
  type LitCtx (Dup expr1 expr2) a = (LitCtx expr1 a, LitCtx expr2 a)

instance (Lit (expr1 h d), Lit (expr2 h d)) => Lit (DupPT expr1 expr2 h d) where
  type LitCtx (DupPT expr1 expr2 h d) a = (LitCtx (expr1 h d) a, LitCtx (expr2 h d) a)

instance (TunnelPT expr1, TunnelPT expr2) => TunnelPT (DupPT expr1 expr2) where

  type TunnelCtxPT (DupPT expr1 expr2) d t e r s zp = (TunnelCtxPT expr1 d t e r s zp, TunnelCtxPT expr2 d t e r s zp)
  type TunnHintType (DupPT expr1 expr2) d t e r s zp = (TunnHintType expr1 d t e r s zp, TunnHintType expr2 d t e r s zp)


instance (SymCT expr1, SymCT expr2) => SymCT (Dup expr1 expr2) where
  type AdditiveCtxCT  (Dup expr1 expr2) ct     =
    (AdditiveCtxCT expr1 ct, AdditiveCtxCT expr2 ct)
  type RingCtxCT      (Dup expr1 expr2) ct     =
    (RingCtxCT expr1 ct, RingCtxCT expr2 ct)
  type ModSwitchCtxCT (Dup expr1 expr2) ct zp' =
    (ModSwitchCtxCT expr1 ct zp', ModSwitchCtxCT expr2 ct zp')
  type RescaleCtxCT   (Dup expr1 expr2) ct zq' =
    (RescaleCtxCT expr1 ct zq', RescaleCtxCT expr2 ct zq')
  type AddPubCtxCT    (Dup expr1 expr2) ct     =
    (AddPubCtxCT expr1 ct, AddPubCtxCT expr2 ct)
  type MulPubCtxCT    (Dup expr1 expr2) ct     =
    (MulPubCtxCT expr1 ct, MulPubCtxCT expr2 ct)
  type KeySwitchCtxCT (Dup expr1 expr2) ct zq' gad =
    (KeySwitchCtxCT expr1 ct zq' gad, KeySwitchCtxCT expr2 ct zq' gad)
  type TunnelCtxCT    (Dup expr1 expr2) t e r s e' r' s' zp zq gad =
    (TunnelCtxCT expr1 t e r s e' r' s' zp zq gad,
     TunnelCtxCT expr2 t e r s e' r' s' zp zq gad)

  (Dup a1 a2) +^ (Dup b1 b2) = Dup (a1 +^ b1) (a2 +^ b2)

  negCT (Dup a b) = Dup (negCT a) (negCT b)

  (Dup a1 a2) *^ (Dup b1 b2) = Dup (a1 *^ b1) (a2 *^ b2)

  modSwitchPT (Dup a b) = Dup (modSwitchPT a) (modSwitchPT b)

  rescaleCT (Dup a b) = Dup (rescaleCT a) (rescaleCT b)

  addPublicCT a (Dup b c) = Dup (addPublicCT a b) (addPublicCT a c)

  mulPublicCT a (Dup b c) = Dup (mulPublicCT a b) (mulPublicCT a c)

  keySwitchQuadCT a (Dup b c) = Dup (keySwitchQuadCT a b) (keySwitchQuadCT a c)

  tunnelCT a (Dup b c) = Dup (tunnelCT a b) (tunnelCT a c)


-- EAC: undefined is very suspect here. It seems to be due to the fact that the
-- (Dup a -> Dup b) function could in theory mix the two components together.
instance (Lambda expr1, Lambda expr2) => Lambda (Dup expr1 expr2) where
  lam f = Dup (lam $ unDupA . f . flip Dup undefined) (lam $ unDupB . f . Dup undefined)

  app (Dup fa fb) (Dup a b) = Dup (app fa a) (app fb b)

type family Fsts xs where
  Fsts '[] = '[]
  Fsts ((a,b) ': xs) = (a ': Fsts xs)

type family Snds xs where
  Snds '[] = '[]
  Snds ((a,b) ': xs) = (b ': Snds xs)

instance (LambdaD expr1 (Fsts hs), LambdaD expr2 (Snds hs)) => LambdaD (DupPT expr1 expr2) hs where