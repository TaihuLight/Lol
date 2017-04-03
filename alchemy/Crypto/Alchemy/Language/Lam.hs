{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Crypto.Alchemy.Language.Lam where

import Crypto.Alchemy.Depth
import Data.Singletons.Prelude.List

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b


-- | Lambda abstraction and application for leveled computations.

class LambdaD expr (h :: [*]) where
  -- | Abstract.
  lamD :: (expr '[] da a -> expr h db b) -> expr h ('L da db) (a -> b)

  -- | Apply.
  appD :: expr h' ('L da db) (a -> b) -> expr h da a -> expr (h :++ h') db b
