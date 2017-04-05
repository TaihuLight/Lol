{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
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

import Data.Constraint           hiding ((***), (&&&))
import Data.Dynamic
import Data.Maybe (mapMaybe)
import Data.Type.Natural (Nat(..))
import Data.Singletons.Prelude.List ((:++))
import GHC.TypeLits hiding (type (*), Nat)-- for error message


import Unsafe.Coerce

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

data PT2CT :: [(Factored,Factored)] -- map from plaintext index to ciphertext index
           -> [*]                   -- list of ciphertext moduli, smallest first
                                    --   e.g. '[ Zq 7, (Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))]
                                    --   Nesting order matters for efficiency!
           -> [(*,*)]               -- map from ciphertext modulus to corresponding hint modulus
                                    --   e.g. '[ '(Zq 7, (Zq 11, Zq 7))]
                                    --   Nesting order matters for efficiency!
           -> *                     -- gadget for key switching
           -> *                     -- variance type
           -> (* -> *)              -- ciphertext interpreter
           -> [*]                   -- Hint parameters
           -> Depth                 -- (multiplicative) depth of the computation
                                    --   n.b. This should usually be ('T 'Z) in top level code.
           -> *                     -- type contained in the expression
           -> * where
  P2C :: {runP2C :: ctexpr (CTType m'map zqs d a)} -> PT2CT m'map zqs zq'map gad v ctexpr '[] d a
  GenKSH :: (GetKSHintCtx gad v t m' z zq') =>
    Proxy z
    -> (KSHintDummy gad v t m' z zq' -> PT2CT m'map zqs zq'map gad v ctexpr hs d a)
    -> PT2CT m'map zqs zq'map gad v ctexpr ((KSHintDummy gad v t m' z zq') ': hs) d a
  {-GenTH :: (GetTunnHintCtx t e r s e' r' s' z zp zq gad v) =>
    Proxy z
    -> Linear t zp e r s
    -> (TunnelInfo gad t e r s e' r' s' zp zq -> PT2CT m'map zqs zq'map gad v ctexpr hs d a)
    -> PT2CT m'map zqs zq'map gad v ctexpr ((TunnelInfo gad t e r s e' r' s' zp zq) ': hs) d a-}


data KSHintDummy gad v t m' z zq' = KSH (KSQuadCircHint gad (Cyc t m' zq'))

-- explicit forall for type application
compile' :: forall m'map zqs zq'map gad v ctexpr d a rnd mon h .
  (MonadRandom rnd, mon ~ ReaderT v (StateT ([Dynamic],[Dynamic]) rnd))
  => PT2CT m'map zqs zq'map gad v ctexpr h d a -> mon (ctexpr (CTType m'map zqs d a))
compile' (P2C b) = return b
compile' (GenKSH z b) = do
          hint <- getKSHint z
          compile' $ b $ KSH hint

compile :: forall m'map zqs zq'map gad v ctexpr d a rnd mon h .
  (MonadRandom rnd, mon ~ ReaderT v (StateT ([Dynamic],[Dynamic]) rnd))
  => v -> mon (PT2CT m'map zqs zq'map gad v ctexpr h d a) -> rnd (ctexpr (CTType m'map zqs d a), ([Dynamic],[Dynamic]))
compile v a =
  flip runStateT ([],[]) $ flip runReaderT v $ do
    a' <- a
    compile' a'

-- this function prevents explosions of cases in binary operators with multiple GADT constructors
push :: PT2CT m'map zqs zq'map gad v ctexpr h1 d1 a
        -> (ctexpr (CTType m'map zqs d1 a) -> PT2CT m'map zqs zq'map gad v ctexpr h2 d2 b)
        -> PT2CT m'map zqs zq'map gad v ctexpr (h1 :++ h2) d2 b
push (P2C a) f = f a
push (GenKSH z g) f = GenKSH z $ \h -> push (g h) f
--push (GenTH z g h) f = GenTH z g $ \i -> push (h i) f

p2cmap :: (ctexpr (CTType m'map zqs d a) -> ctexpr (CTType m'map zqs d' b))
  -> PT2CT m'map zqs zq'map gad v ctexpr h d a
  -> PT2CT m'map zqs zq'map gad v ctexpr h d' b
p2cmap f a = push a (P2C . f) \\ appEmpty a

-- convinces the compiler that (h ++ '[] ~ h)
-- a possible solution is to be able to prepend to type lists rather than post-pend
-- I haven't figured out how to make that work yet.
appEmpty :: forall f h d a . f h d a -> (() :- (h ~ (h :++ '[])))
appEmpty _ = Sub $ unsafeCoerce (Dict :: Dict ())

---- Language instances

instance (SymCT ctexpr) => AddPT (PT2CT m'map zqs zq'map gad v ctexpr) where

  type AddPubCtxPT   (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (AddPubCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))
  type MulPubCtxPT   (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (MulPubCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))
  type AdditiveCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (AdditiveCtxCT ctexpr (CT m zp (Cyc t (Lookup m m'map) (zqs !! d))))

{-
-- EAC: this suffices, but it's not pretty.
-- On the other hand, GHC can tell the output list matches,
-- so I don't need the (unsafeCoerce) entailment
  (P2C a) +# (P2C b) = P2C $ a +^ b
  (GenKSH z f) +# b = GenKSH z $ \h -> f h +# b
  (GenTH z f a) +# b = GenTH z f $ (\h -> a h +# b)
  a@(P2C _) +# (GenKSH z f) = GenKSH z $ \h -> a +# f h
  a@(P2C _) +# (GenTH z f b) = GenTH z f $ \h -> a +# b h
-}
  a +# b = (push a $ \a' -> push b $ \b' ->
    P2C $ a' +^ b') \\ appEmpty b
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

instance (SymCT ctexpr) => MulPT (PT2CT m'map zqs zq'map gad v ctexpr) where
  type RingCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp) =
    (RingCtxPT' ctexpr t m (Lookup m m'map) (LiftOf zp) zp (zqs !! d) (zqs !! (Add1 d)) zq'map gad v)

  type KSHintType (PT2CT m'map zqs zq'map gad v ctexpr) d (Cyc t m zp)
    = KSHintDummy gad v t (Lookup m m'map) (LiftOf zp) (Lookup (zqs !! (Add1 d)) zq'map)

  -- EAC: should key switch before the mul, only if necessary. Current signature of *# doesn't allow this...
  (*#) :: forall rp t m zp d' zq expr d h1 h2 m' .
       (rp ~ Cyc t m zp, d' ~ Add1 d, zq ~ (zqs !! d'), m' ~ Lookup m m'map,
        expr ~ PT2CT m'map zqs zq'map gad v ctexpr, RingCtxPT expr d (Cyc t m zp))
       => expr h1 d' rp -> expr h2 d' rp ->
          expr (h1 :++ h2 :++ '[KSHintDummy gad v t m' (LiftOf zp) (Lookup (zqs !! (Add1 d)) zq'map)]) d rp
  a *# b = (push a $ \a' -> push b $ \b' ->
    -- EAC: the fact that I need a signature here seems like a bug.
    GenKSH Proxy $ \(KSH h :: KSHintDummy gad v t m' (LiftOf zp) (Lookup zq zq'map)) -> P2C $ rescaleCT $ keySwitchQuadCT h $ a' *^ b') \\ appEmpty b

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

  tunnelPT :: forall d t e r s zp h .
    (TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d t e r s zp)
    => Linear t zp e r s -> mon (PT2CT m'map zqs zq'map gad v ctexpr h d (Cyc t r zp)
                                 -> PT2CT m'map zqs zq'map gad v ctexpr h d (Cyc t s zp))
  tunnelPT f = do
    thint <- genTunnHint @gad @(LiftOf zp) @(zqs !! (Add1 d)) Proxy f
    return $ p2cmap (rescaleCT . tunnelCT thint . rescaleCT)
{-
instance (SymCT ctexpr)
  => TunnelPT (PT2CT m'map zqs zq'map gad v ctexpr) where
  type TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d t e r s zp =
    (TunnelCtxPT' ctexpr t e r s (Lookup r m'map) (Lookup s m'map) (LiftOf zp) zp (zqs !! d) (zqs !! (Add1 d)) gad v)
  type TunnHintType (PT2CT m'map zqs zq'map gad v ctexpr) d t e r s zp =
    TunnelInfo gad t e r s (e * ((Lookup r m'map) / r)) (Lookup r m'map) (Lookup s m'map) zp (zqs !! (Add1 d))

  tunnelPT :: forall d t e r s zp hs .
    (TunnelCtxPT (PT2CT m'map zqs zq'map gad v ctexpr) d t e r s zp)
    => Linear t zp e r s -> PT2CT m'map zqs zq'map gad v ctexpr hs d (Cyc t r zp)
                                 -> PT2CT m'map zqs zq'map gad v ctexpr (hs :++ '[TunnHintType (PT2CT m'map zqs zq'map gad v ctexpr) d t e r s zp]) d (Cyc t s zp)
  tunnelPT f a = (push a (\a' ->
    -- EAC: the fact that I need a signature here seems like a bug.
    GenTH Proxy f $ \(h :: TunnelInfo _ _ _ _ _ _ _ _ _ (zqs !! (Add1 d))) ->
      P2C $ rescaleCT $ tunnelCT h $ rescaleCT a')) \\ appEmpty a
-}
instance (Lambda ctexpr) => LambdaD (PT2CT m'map zqs zq'map gad v ctexpr) '[] where
  lamD f = P2C $ lam $ runP2C . f . P2C
  appD (P2C f) a = p2cmap (app f) a
  appD (GenKSH z f) a = GenKSH z $ \h -> appD (f h) a

-- EAC: this is terrible. I don't want multiple Lambda instances for different hint types
instance (Lambda ctexpr, GetKSHintCtx gad v t m' z zq', LambdaD (PT2CT m'map zqs zq'map gad v ctexpr) hs)
  => LambdaD (PT2CT m'map zqs zq'map gad v ctexpr) ((KSHintDummy gad v t m' z zq') ': hs) where

  lamD f = GenKSH Proxy $ \h -> lamD $ \a ->
    case f a of
      GenKSH _ b -> b h
  appD f (GenKSH z a) = GenKSH z $ appD f . a

{-
(GetTunnHintCtx t e r s e' r' s' z zp zq gad v) =>
    Proxy z
    -> Linear t zp e r s
    -> (TunnelInfo gad t e r s e' r' s' zp zq -> PT2CT m'map zqs zq'map gad v ctexpr hs d a)
    -> PT2CT m'map zqs zq'map gad v ctexpr ((TunnelInfo gad t e r s e' r' s' zp zq) ': hs) d a

instance (GetTunnHintCtx t e r s e' r' s' z zp zq gad v,
          Lambda ctexpr, LambdaD (PT2CT m'map zqs zq'map gad v ctexpr) hs)
  => LambdaD (PT2CT m'map zqs zq'map gad v ctexpr) ((TunnelInfo gad t e r s e' r' s' zp zq) ': hs) where

  lamD f = GenTH Proxy g $ \h -> lamD $ \a ->
    case f a of
      GenTH _ g b -> b h
  appD f (GenTH z g a) = GenTH z g $ appD f . a
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

-- EAC: https://ghc.haskell.org/trac/ghc/ticket/13490
type GetTunnHintCtx t e r s e' r' s' z zp zq gad v =
  (GenSKCtx t r' z v, Typeable (Cyc t r' z),
   GenSKCtx t s' z v, Typeable (Cyc t s' z),
   GenTunnelInfoCtx t e r s e' r' s' z zp zq gad)

-- not memoized right now, but could be if we also store the linear function as part of the lookup key
genTunnHint :: forall gad z zq mon t e r s e' r' s' zp v .
  (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon, MonadRandom mon,
   GetTunnHintCtx t e r s e' r' s' z zp zq gad v)
  => Proxy z -> Linear t zp e r s -> mon (TunnelInfo gad t e r s e' r' s' zp zq)
genTunnHint _ linf = do
  skout <- getKey @z
  sk <- getKey @z
  tunnelInfo linf skout sk

type GetKSHintCtx gad v t m' z zq' =
  (GenSKCtx t m' z v, Typeable (Cyc t m' z),
   -- constraints for hintLookup
   Typeable (KSQuadCircHint gad (Cyc t m' zq')),
   -- constraints for ksQuadCircHint
   KSHintCtx gad t m' z zq')

-- retrieve a key-switch hint from the state, or generate a new one otherwise
getKSHint :: forall v mon t z gad m' zq' .
  (-- constraints for getKey
   MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
   MonadRandom mon, GetKSHintCtx gad v t m' z zq')
  => Proxy z -> mon (KSQuadCircHint gad (Cyc t m' zq'))
getKSHint _ = hintLookup >>= \case
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
