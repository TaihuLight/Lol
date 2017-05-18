{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Crypto.Alchemy.Language.LinearCyc where

import Crypto.Alchemy.Language.Lambda
import Crypto.Lol
import GHC.Exts                       (Constraint)

-- | Symantics for evaluating a linear function on cyclotomics.

class LinearCyc expr linrep cycrep where

  -- | Constraints needed to linear
  type LinearCycCtx expr linrep cycrep
         (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  -- | 'Cyc' wrapper for the input to linearing
  type PreLinearCyc expr cycrep :: Factored -> * -> *

  -- | An object-language expression representing the given linear function.
  linearCyc_ :: (LinearCycCtx expr linrep cycrep e r s zp)
    => linrep e r s zp
    -> expr env (PreLinearCyc expr cycrep r zp -> cycrep s zp)

linearCyc :: (LinearCyc expr linrep cycrep,
              LinearCycCtx expr linrep cycrep e r s zp, Lambda expr)
  => linrep e r s zp
  -> expr env (PreLinearCyc expr cycrep r zp)
  -> expr env (cycrep s zp)
linearCyc f a = linearCyc_ f $: a
