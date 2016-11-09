{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

import Control.Monad.Random

import Crypto.Lol (Cyc)
import Crypto.Lol.Applications.SymmSHE hiding (CT)
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Cyclotomic.Tensor.Repa
import Crypto.Lol.Factored
import Crypto.Lol.Gadget
import Crypto.Lol.Tests (testGroupM)
import Crypto.Lol.Types

import Data.Int
import Data.Proxy

import HomomPRFTests
import KHPRFTests
import SHETests
import Test.Framework

infixr 9 **
data a ** b

type family Zq (a :: k) :: * where
  Zq (a ** b) = (Zq a, Zq b)
  Zq q = (ZqBasic q Int64)

main :: IO ()
main = do
  flip defaultMainWithArgs ["--threads=1","--maximum-generated-tests=100"] $ concat
    [defaultTests (Proxy::Proxy CT) (Proxy::Proxy TrivGad),
     defaultTests (Proxy::Proxy RT) (Proxy::Proxy TrivGad)]

defaultTests :: _ => Proxy t -> Proxy gad -> [Test]
defaultTests pt pgad  =
  [testGroupM "SHE" $ concat $ ($ pt) <$> [
    sheTests (Proxy::Proxy '(F7, F7, Zq 2,Zq (19393921 ** 18869761))),
    sheTests (Proxy::Proxy '(F7, F21,Zq 2,Zq (19393921 ** 18869761))),
    sheTests (Proxy::Proxy '(F2, F8, Zq 2,Zq 536871001)),
    sheTests (Proxy::Proxy '(F1, F8, Zq 2,Zq 536871001)),
    sheTests (Proxy::Proxy '(F4, F12,Zq 2,Zq 2148249601)),
    sheTests (Proxy::Proxy '(F4, F8, Zq 3,Zq 2148249601)),
    sheTests (Proxy::Proxy '(F7, F7, Zq 4,Zq (19393921 ** 18869761))),
    sheTests (Proxy::Proxy '(F7, F21,Zq 4,Zq (19393921 ** 18869761))),
    sheTests (Proxy::Proxy '(F1, F4, Zq 4,Zq 18869761)),
    sheTests (Proxy::Proxy '(F4, F4, Zq 4,Zq 18869761)),
    sheTests (Proxy::Proxy '(F14,F14,Zq 4,Zq 18869761)),
    sheTests (Proxy::Proxy '(F28,F28,Zq 4,Zq 18869761)),
    sheTests (Proxy::Proxy '(F28,F28,Zq 4,Zq 80221)),
    sheTests (Proxy::Proxy '(F1, F8, Zq 4,Zq 536871001)),
    sheTests (Proxy::Proxy '(F2, F8, Zq 4,Zq 536871001)),
    sheTests (Proxy::Proxy '(F4, F12,Zq 8,Zq 2148249601)),

    decTest (Proxy::Proxy '(F2, F8, Zq 2,Zq 536871001)),
    decTest (Proxy::Proxy '(F1, F8, Zq 2,Zq 536871001)),
    decTest (Proxy::Proxy '(F4, F12,Zq 2,Zq 2148249601)),
    decTest (Proxy::Proxy '(F4, F8, Zq 3,Zq 2148249601)),
    decTest (Proxy::Proxy '(F1, F4, Zq 4,Zq 18869761)),
    decTest (Proxy::Proxy '(F4, F4, Zq 4,Zq 18869761)),
    decTest (Proxy::Proxy '(F14,F14,Zq 4,Zq 18869761)),
    decTest (Proxy::Proxy '(F28,F28,Zq 4,Zq 18869761)),
    decTest (Proxy::Proxy '(F28,F28,Zq 4,Zq 80221)),
    decTest (Proxy::Proxy '(F1, F8, Zq 4,Zq 536871001)),
    decTest (Proxy::Proxy '(F2, F8, Zq 4,Zq 536871001)),
    decTest (Proxy::Proxy '(F4, F12,Zq 8,Zq 2148249601)),

    modSwPTTest (Proxy::Proxy '(F7,F21,Zq 4,Zq 8,Zq 18869761)),
    modSwPTTest (Proxy::Proxy '(F7,F42,Zq 2,Zq 4,Zq (18869761 ** 19393921))),

    ksTests (Proxy::Proxy '(F1, F7,  Zq 2, Zq 19393921,   Zq (19393921 ** 18869761))) pgad,
    ksTests (Proxy::Proxy '(F2, F4,  Zq 8, Zq 2148854401, Zq (2148854401 ** 2148249601))) pgad,
    ksTests (Proxy::Proxy '(F4, F12, Zq 2, Zq 2148854401, Zq (2148854401 ** 2148249601))) pgad,
    ksTests (Proxy::Proxy '(F8, F64, Zq 2, Zq 2148854401, Zq (2148854401 ** 2148249601))) pgad,
    ksTests (Proxy::Proxy '(F3, F27, Zq 2, Zq 2148854401, Zq (2148854401 ** 2148249601))) pgad,
    ksTests (Proxy::Proxy '(F2, F4,  Zq 8, Zq 2148854401, Zq (2148854401 ** 2148249601 ** 2150668801))) pgad,
    ksTests (Proxy::Proxy '(F4, F12, Zq 2, Zq 2148854401, Zq (2148854401 ** 2148249601 ** 2150668801))) pgad,
    ksTests (Proxy::Proxy '(F8, F64, Zq 2, Zq 2148854401, Zq (2148854401 ** 2148249601 ** 2150668801))) pgad,
    ksTests (Proxy::Proxy '(F3, F27, Zq 2, Zq 2148854401, Zq (2148854401 ** 2148249601 ** 2150668801))) pgad,

    twemTests (Proxy::Proxy '(F1, F7, F3, F21, Zq 2, Zq 18869761)),

    tunnelTests (Proxy::Proxy '(F8,F40,F20,F60,Zq 4,Zq (18869761 ** 19393921))) pgad],
  testGroupM "KHPRF" $ concat $ ($ pt) <$> [
    khprfTests (Proxy::Proxy '(F32, Zq 2, Zq 8, BaseBGad 2)),
    khprfTests (Proxy::Proxy '(F32, Zq 2, Zq 8, TrivGad)),
    khprfTests (Proxy::Proxy '(F32, Zq 32, Zq 257, BaseBGad 2))],
  testGroupM "HomomPRF" $ concat $ ($ pt) <$> [
    homomPRFTests 5 (Proxy::Proxy '(RngList, ZP8, ZQ4, ZQSeq, PRFGad, KSGad))]
  ]

-- homomPRF params
type H0 = F128
type H1 = F64 * F7
type H2 = F32 * F7 * F13
type H3 = F8 * F5 * F7 * F13
type H4 = F4 * F3 * F5 * F7 * F13
type H5 = F9 * F5 * F7 * F13
type H0' = H0 * F7 * F13
type H1' = H1 * F13
type H2' = H2
type H3' = H3
type H4' = H4
type H5' = H5
type RngList = '[ '(H0,H0'), '(H1,H1'), '(H2,H2'), '(H3,H3'), '(H4,H4'), '(H5,H5') ]

-- three 24-bit moduli, enough to handle rounding for p=32 (depth-4 circuit at ~17 bits per mul)
type ZQ1 = Zq 18869761
type ZQ2 = (Zq 19393921, ZQ1)
type ZQ3 = (Zq 19918081, ZQ2)
-- a 31-bit modulus, for rounding off after the last four hops
type ZQ4 = (Zq 2149056001, ZQ3)
-- for rounding off after the first hop
type ZQ5 = (Zq 3144961, ZQ4)
type ZQ6 = (Zq 7338241, ZQ5)
type ZQSeq = '[ZQ6, ZQ5, ZQ4, ZQ3, ZQ2, ZQ1]

type ZP8 = Zq PP8

-- these need not be the same
type KSGad = BaseBGad 2
type PRFGad = BaseBGad 2

-- EAC: is there a simple way to parameterize the variance?
-- generates a secret key with scaled variance 1.0
instance (GenSKCtx t m' z Double) => Random (SK (Cyc t m' z)) where
  random = runRand $ genSK (1 :: Double)
  randomR = error "randomR not defined for SK"