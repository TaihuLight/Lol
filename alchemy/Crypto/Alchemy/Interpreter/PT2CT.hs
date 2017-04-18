{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTSyntax            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Interpreter.PT2CT where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State.Strict

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.CT
import Crypto.Alchemy.Language.ModSwPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Applications.SymmSHE hiding (tunnelCT, modSwitchPT)

import Data.Dynamic
import Data.Maybe (mapMaybe)
import Data.Type.Natural (Nat(..))
import GHC.TypeLits hiding (type (*))-- for error message

-- singletons exports (:!!), which takes a TypeLit index; we need a TypeNatural index
type family (xs :: [k1]) !! (d :: Depth) :: k1 where
  (x ': xs) !! ('T 'Z) = x
  (x ': xs) !! ('T ('S s)) = xs !! ('T s)
  '[]       !! s = TypeError ('Text "Type-level index-out-of-bounds error for (!!). \
    \You probably need more moduli in your zqs list, or need to correct the computation depth.")

-- a type-lvel map from PT index to CT index
type family Lookup m map where
  Lookup m ( '(m,m') ': rest) = m'
  Lookup r ( '(m,m') ': rest) = Lookup r rest
  Lookup a '[] = TypeError ('Text "Could not find " ':<>: 'ShowType a ':$$: 'Text " in a map Lookup.")

type family CTType m'map zqs d a where
  CTType m'map zqs d (Cyc t m zp) = CT m zp (Cyc t (Lookup m m'map) (zqs !! d))
  CTType m'map zqs ('L da db) (a -> b) = CTType m'map zqs da a -> CTType m'map zqs db b
  CTType m'map zqs d c = TypeError ('Text "Cannot compile a plaintext expression over " ':$$: 'ShowType c)

newtype PT2CT :: [(Factored,Factored)] -- map from plaintext index to ciphertext index
           -> [*]                      -- list of ciphertext moduli, smallest first
                                       --   e.g. '[ Zq 7, (Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))]
                                       --   Nesting order matters for efficiency!
           -> [(*,*)]                  -- map from ciphertext modulus to corresponding hint modulus
                                       --   e.g. '[ '(Zq 7, (Zq 11, Zq 7))]
                                       --   Nesting order matters for efficiency!
           -> *                        -- gadget for key switching
           -> *                        -- variance type
           -> (* -> *)                 -- ciphertext interpreter
           -> Depth                    -- (multiplicative) depth of the computation
                                       --   n.b. This should usually be ('T 'Z) in top level code.
           -> *                        -- type contained in the expression
           -> * where
  P2C :: {runP2C :: ctexpr (CTType m'map zqs d a)} -> PT2CT m'map zqs zq'map gad v ctexpr d a

p2cmap :: (Functor i) => (ctexpr (CTType m'map zqs d a) -> ctexpr (CTType m'map zqs d' b))
           -> i (PT2CT m'map zqs zq'map gad v ctexpr d a)
           -> i (PT2CT m'map zqs zq'map gad v ctexpr d' b)
p2cmap f a = P2C <$> f <$> runP2C <$> a

-- hidden constructor
newtype CustomMonad v (rnd :: * -> *) a = CMon {unCMon :: ReaderT v (StateT ([Dynamic],[Dynamic]) rnd) a}
  deriving (Functor, Applicative, Monad, MonadReader v, MonadState ([Dynamic],[Dynamic]), MonadRandom)

-- hidden constructor
newtype PT2CTState = St ([Dynamic],[Dynamic])

-- explicit forall for type application
compile :: forall m'map zqs zq'map gad v ctexpr d a rnd .
  (MonadRandom rnd)
  => v -> ((CustomMonad v rnd) :. Identity) (PT2CT m'map zqs zq'map gad v ctexpr d a) -> rnd (ctexpr (CTType m'map zqs d a), PT2CTState)
compile v a = do
  (b,s) <- flip runStateT ([],[]) $ flip runReaderT v $ unCMon $ runIdentity <$> unJ a
  return (runP2C b, St s)

-- idea: if we create a CT with a type that doesn't appear in
  -- The following sig means we can't give ctexpr a Lit instance
--encryptArg :: PT2CTState -> Cyc t m zp -> ctexpr (CT m zp (Cyc t m' zq))
--encryptArg

---- Language instances

instance (SymCT ctexpr) => AddPT (PT2CT m'map zqs zq'map gad v ctexpr) where

  type AddPubCtxPT   i (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (AddPubCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))), Functor i)
  type MulPubCtxPT   i (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (MulPubCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))), Functor i)
  type AdditiveCtxPT i (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (AdditiveCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))), Applicative i)

  a +# b = P2C <$> ((+^) <$> (runP2C <$> a) <*> (runP2C <$> b))
  negPT = p2cmap negCT
  addPublicPT = p2cmap . addPublicCT
  mulPublicPT = p2cmap . mulPublicCT

type RingCtxPT' ctexpr t m m' z zp zq zq' zq'map gad v =
  (RingCtxCT ctexpr (CT m zp (Cyc t m' zq')),
   RescaleCtxCT ctexpr (CT m zp (Cyc t m' zq)) zq',
   KeySwitchCtxCT ctexpr (CT m zp (Cyc t m' zq')) (Lookup zq' zq'map) gad,
   GenSKCtx t m' z v,
   KSHintCtx gad t m' z (Lookup zq' zq'map),
   Typeable (Cyc t m' z),
   Typeable (KSQuadCircHint gad (Cyc t m' (Lookup zq' zq'map))))

instance (SymCT ctexpr)
  => MulPT (PT2CT m'map zqs zq'map gad v ctexpr) where
  type RingCtxPT i (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (RingCtxPT' ctexpr t m (Lookup m m'map) (LiftOf zp) zp (zqs !! d) (zqs !! (Add1 d)) zq'map gad v,
     MonadRandom i, MonadReader v i, MonadState ([Dynamic],[Dynamic]) i)

  -- EAC: should key switch before the mul, only if necessary. Current signature of *# doesn't allow this...
  (*#) :: forall rp t m zp zqid zq expr d i j .
       (rp ~ Cyc t m zp, zqid ~ Add1 d, zq ~ (zqs !! zqid), Applicative j,
        expr ~ PT2CT m'map zqs zq'map gad v ctexpr, RingCtxPT i expr d (Cyc t m zp))
       => (i :. j) (expr zqid rp) -> (i :. j) (expr zqid rp) -> (i :. j) (expr d rp)
  a *# b = do -- in the (i :. j) applicative
    a' <- runP2C <$> a
    b' <- runP2C <$> b
    hint :: KSQuadCircHint gad (Cyc t (Lookup m m'map) (Lookup zq zq'map)) <- liftJ $ getKSHint (Proxy::Proxy zq'map) (Proxy::Proxy (LiftOf zp)) (Proxy::Proxy zq)
    return $ P2C $ rescaleCT $ keySwitchQuadCT hint $ a' *^ b'
    --(\a' b' (hint :: KSQuadCircHint gad (Cyc t (Lookup m m'map) (Lookup zq zq'map))) -> P2C $ rescaleCT $ keySwitchQuadCT hint $ a' *^ b') <$> (runP2C <$> a) <*> (runP2C <$> b) <*> (liftJ $ getKSHint (Proxy::Proxy zq'map) (Proxy::Proxy (LiftOf zp)) (Proxy::Proxy zq))
{-
instance (SymCT ctexpr) => ModSwPT (PT2CT m'map zqs zq'map gad v ctexpr) where
  type ModSwitchCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) zp' =
    (ModSwitchCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))) zp')

  modSwitchDec = p2cmap modSwitchPT

type TunnelCtxPT' ctexpr t e r s r' s' z zp zq zq' gad v =
  (TunnelCtxCT ctexpr t e r s (e * (r' / r)) r' s'   zp zq' gad,
   GenTunnelInfoCtx   t e r s (e * (r' / r)) r' s' z zp zq' gad,
   GenSKCtx t r' z v, GenSKCtx t s' z v,
   Typeable t, Typeable r', Typeable s', Typeable z, -- bug; see genTunnHint
   RescaleCtxCT ctexpr (CT r zp (Cyc t r' zq')) zq, RescaleCtxCT ctexpr (CT s zp (Cyc t s' zq)) zq')

instance (SymCT ctexpr, MonadRandom mon, MonadReader v mon, MonadState ([Dynamic],[Dynamic]) mon)
  => TunnelPT mon (PT2CT m'map zqs zq'map gad v ctexpr) where
  type TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d t e r s zp =
    (TunnelCtxPT' ctexpr t e r s (Lookup r m'map) (Lookup s m'map) (LiftOf zp) zp (zqs !! d) (zqs !! (Add1 d)) gad v)

  tunnelPT :: forall d t e r s zp .
    (TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d t e r s zp)
    => Linear t zp e r s -> mon (PT2CT m'map zqs zq'map gad v ctexpr d (Cyc t r zp)
                                 -> PT2CT m'map zqs zq'map gad v ctexpr d (Cyc t s zp))
  tunnelPT f = do
    thint <- genTunnHint @gad @(zqs !! (Add1 d)) f
    return $ p2cmap (rescaleCT . tunnelCT thint . rescaleCT)

lam' :: (Functor m, Applicative i, Lambda expr) =>
  (forall j . (Applicative j) => (i :. j) (expr a) -> (m :. (i :. j)) (expr b))
    -> (m :. i) (expr (a -> b))
lam' f = fmap lam (J $ fmap unJ $ unJ $ f (J $ pure id))
-}

instance (Lambda ctexpr) => LambdaD (PT2CT m'map zqs zq'map gad v ctexpr) where

  -- EAC: Should be able to use lam', which is identical to the code I wrote below, but the compiler won't have it.
  lamD f =
    let f' x = runP2C <$> f (P2C <$> x)
    in P2C <$> (fmap lam (J $ fmap unJ $ unJ $ f' (J $ pure $ id)))

  appD f x = P2C <$> (app <$> (runP2C <$> f) <*> (runP2C <$> x))

{-  :: (forall j. AppLiftable j => (i :. j) (repr da a) -> (m :. (i :. j)) (repr db b))
          -> (m :. i) (repr ('L da db) (a->b))
}
j ~ ((->) ctexpr a)
id :: (ctexpr a -> ctexpr a) ~ j (ctexpr a)
pure id :: i (j (ctexpr a))
J $ .. :: (i :. j) (ctexpr a)
unJ $ f ... :: m ((i :. j) (ctexpr ))
-}

{-
-- newtype (i :. j) a = J{unJ:: i (j a)}
lam :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) =>
       (forall j. AppLiftable j =>
        (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
       -> (m :. i) (repr (a->b))
lam f = fmap lamS (J $ fmap unJ $ unJ $ f  (J $ pure $ v))
 where
 -- instantiate applicative j to be a Reader: repr a -> w
 v = \repra -> repra                    -- bound variable



-- j ~ ((->) (repr a))
-- v :: repr a -> repr a
-- v ~ j (repr a)

-- pure v :: i (j (repr a))
-- J $ pure v :: (i :. j) (repr a)
-- unJ $ f ... :: m ((i :. j) (repr b))
-- fmap unJ $ unJ $ f ... :: m (i (j (repr b)))
-- J $ fmap unJ $ unJ $ f ... :: (m :. i) (j (repr b)) ~ (m :. i) (repr a -> repr b)
-- fmap lamS ... :: (m :. i) (repr (a -> b))





-- a simpler type is possible if we don't need let-insertion across binders
lamPT :: (Applicative m, AppLiftable i, Lambda repr) =>
       (forall j. AppLiftable j =>
        (i :. j) (repr da a) -> (m :. (i :. j)) (repr db b))
       -> (m :. i) (repr ('L da db) (a->b))
lamPT f = fmap lam $ J . fmap unJ . unJ $ f  $ J . pure $ id
-}






---- Monad helper functions

-- retrieve the scaled variance parameter from the Reader
getSvar :: (MonadReader v mon) => mon v
getSvar = ask

-- retrieve a key from the state, or generate a new one otherwise
getKey :: forall z v mon t m' . (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
           MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z))
  => mon (SK (Cyc t m' z))
getKey = keyLookup >>= \case
  (Just s) -> return s
  -- generate a key with the variance stored in the Reader monad
  Nothing -> genSK =<< getSvar

-- not memoized right now, but could be if we also store the linear function as part of the lookup key
-- EAC: https://ghc.haskell.org/trac/ghc/ticket/13490
genTunnHint :: forall gad zq mon t e r s e' r' s' z zp v .
  (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon, MonadRandom mon,
   GenSKCtx t r' z v, Typeable (Cyc t r' (LiftOf zp)),
   GenSKCtx t s' z v, Typeable (Cyc t s' (LiftOf zp)),
   GenTunnelInfoCtx t e r s e' r' s' z zp zq gad,
   z ~ LiftOf zp)
  => Linear t zp e r s -> mon (TunnelInfo gad t e r s e' r' s' zp zq)
genTunnHint linf = do
  skout <- getKey @z
  sk <- getKey @z
  tunnelInfo linf skout sk

-- retrieve a key-switch hint from the state, or generate a new one otherwise
getKSHint :: forall v mon t z gad m' (zq :: *) zq' map .
  (-- constraints for getKey
   MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
   MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z),
   -- constraints for hintLookup
   Typeable (KSQuadCircHint gad (Cyc t m' zq')),
   -- constraints for ksQuadCircHint
   zq' ~ Lookup zq map, KSHintCtx gad t m' z zq')
  => Proxy map -> Proxy z -> Proxy zq -> mon (KSQuadCircHint gad (Cyc t m' zq'))
getKSHint _ _ _ = hintLookup >>= \case
  (Just h) -> return h
  Nothing -> do
    sk :: SK (Cyc t m' z) <- getKey
    ksQuadCircHint sk

-- lookup a key in the state
keyLookup :: (Typeable a, MonadState ([Dynamic], b) mon) => mon (Maybe a)
keyLookup = (dynLookup . fst) <$> get

-- lookup a hint in the state
hintLookup :: (Typeable a, MonadState (b, [Dynamic]) mon) => mon (Maybe a)
hintLookup = (dynLookup . snd) <$> get

-- lookup an item in a dynamic list
dynLookup :: (Typeable a) => [Dynamic] -> Maybe a
dynLookup ds = case mapMaybe fromDynamic ds of
  [] -> Nothing
  [x] -> Just x
