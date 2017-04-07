{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.EDSL where

import Control.Monad.Identity
import Crypto.Alchemy.Depth
import Crypto.Alchemy.Interpreter.Duplicate
import Crypto.Alchemy.Language.CT ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.ModSwPT ()
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Alchemy.Interpreter.CTEval ()
import Crypto.Alchemy.Interpreter.DeepSeq
import Crypto.Alchemy.Interpreter.DupRescale
import Crypto.Alchemy.Interpreter.PTEval
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.ShowPT
import Crypto.Alchemy.Interpreter.ShowCT

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types
import Crypto.Lol.Cyclotomic.Tensor (TElt) -- EAC: I shouldn't need to explicitly import this
import Crypto.Lol.Types.ZPP -- EAC: I shouldn't need to explicitly import this...

import Data.Type.Natural
import Data.Singletons.Prelude.List

-- type restricted version of `lit` which forces no context on literals
litPT :: (Lit (ptexpr '[] d), LitCtx (ptexpr '[] d) a) => a -> ptexpr '[] d a
litPT = lit



{-
(AddPT ptexpr, MulPT ptexpr, a ~ Cyc t m zp,
 AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
 RingCtxPT ptexpr d a, Ring a, LambdaD ptexpr)
-}
pt1 :: forall t m zp d ptexpr . (_)
  => ptexpr _ ('L (Add1 d) ('L (Add1 d) d)) (Cyc t m zp -> Cyc t m zp -> Cyc t m zp)
pt1 = lamD $ \b -> lamD $ \a -> addPublicPT 2 $ a *# (a +# b)

{-
(AddPT ptexpr, MulPT ptexpr, a ~ Cyc t m zp,
 AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
 RingCtxPT ptexpr d a, Ring a, LambdaD ptexpr)
-}

pt2 :: forall t m zp d ptexpr . (_)
  => Cyc t m zp -> Cyc t m zp -> ptexpr '[KSHintType ptexpr d (Cyc t m zp)] d (Cyc t m zp)
pt2 a b = appD (appD pt1 $ litPT a) $ litPT b

{-
(TunnelPTCtx' expr d mon t eru r u zp,
 TunnelPTCtx' expr d mon t eus u s zp,
 Monad mon, LambdaD expr)
-}

tunn1 :: forall t r u s zp d expr . (_)
  => Proxy u -> expr _ ('L d d) (Cyc t r zp -> Cyc t s zp)
tunn1 _ = lamD $ \x -> tunnelPT' $ tunnelPT' @u x

type Zq q = ZqBasic q Int64
-- pt1 ∷ ∀ {zp} {m ∷ Factored} {t ∷ Factored → ★ → ★} {ptexpr ∷ [GHC.Types.*] → Depth → ★ → ★} {d ∷ Depth}
main :: IO ()
main = do
-- EAC: There's a GHC bug here: GHC *can* infer the type of the signature (e.g., of pt1)
-- when I make it infer the list of hints, but it's mangling the order of the
-- forall'd variables, which is supposed to be sacred. Thus even though I've
-- listed "t m zp d ptexpr" here, GHC apparently expects use sites to use the
-- order "ptexpr d t m zp".
--https://ghc.haskell.org/trac/ghc/ticket/13524

  -- print the unapplied PT function
  putStrLn $ unSPT $ pt1 @ShowPT @('T 'Z) @CT @F4 @Int64  -- @CT @F4 @Int64 @('T 'Z)
  -- apply the PT function to arguments, then print it out
  putStrLn $ unSPT $ pt2 @CT @F4 @Int64 @('T 'Z) 7 11
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ unID $ pt2 @CT @F4 @Int64 7 11
  -- compile the un-applied function to CT, then print it out
  (x,_) <- compile
         @'[ '(F4, F8) ]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         (pt1 @_ @('T 'Z) @CT @F4 @(Zq 7))
  putStrLn $ unSCT x

  -- example with rescale de-duplication when tunneling
  -- print the unapplied PT function
  putStrLn $ unSPT $ tunn1 @H2 @_ @('T 'Z) @CT @H0 @H1 @(Zq PP8) Proxy
  -- compile the up-applied function to CT, then print it out
  (y,_) <- compile
         @'[ '(H0, H0'), '(H1,H1'), '(H2, H2') ]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         (tunn1 @H2 @_ @('T 'Z) @CT @H0 @H1 @(Zq PP8) Proxy)
  -- compile once, interpret with multiple ctexprs!!
  let (z1,z2) = duplicate $ runDeepSeq y
  putStrLn $ unSCT z1
  putStrLn $ unSCT $ runDupRescale z2

type H0 = F8
type H1 = F4 * F7
type H2 = F2 * F7 * F13
type H0' = H0 * F7 * F13
type H1' = H1 * F13
type H2' = H2

-- EAC: This is copied from HomomPRF, but it needs a permanent home.
type TunnelPTCtx' expr d t e r s zp =
  (e ~ FGCD r s,                                     -- type restriction for simplicity
   TunnelPT expr, TunnelCtxPT expr d t e r s zp, -- call to tunnelPT
   e `Divides` r, e `Divides` s, CElt t zp,          -- linearDec
   ZPP zp, TElt t (ZpOf zp))                         -- crtSet
tunnelPT' :: forall s expr t r zp e h d . (TunnelPTCtx' expr d t e r s zp)
  => expr h d (Cyc t r zp) -> expr (h :++ '[TunnHintType expr d t e r s zp]) d (Cyc t s zp)
tunnelPT' =
  let crts = proxy crtSet (Proxy::Proxy e)
      r = proxy totientFact (Proxy::Proxy r)
      e = proxy totientFact (Proxy::Proxy e)
      dim = r `div` e
      -- only take as many crts as we need
      -- otherwise linearDec fails
      linf = linearDec (take dim crts) :: Linear t zp e r s
  in tunnelPT linf
