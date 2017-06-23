{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.Arithmetic where

-- | Addition.

class Add expr a where
  infixl 6 +:, -:

  -- | Addition.
  (+:) :: expr e a -> expr e a -> expr e a

  -- | Subtraction.  (Default implementation is the natural one, using
  -- '(:+)' and 'neg_'.)
  (-:) :: expr e a -> expr e a -> expr e a
  a -: b = a +: (neg_ b)

  -- | Negation.
  neg_ :: expr e a -> expr e a

-- | Addition of (metalanguage) literals to (object language)
-- expressions.

class AddLit expr a where
  (>+:) :: a -> expr e a -> expr e a

-- | Multiplication. (Note that the input type @b@ may differ from the
-- output type @a@.)

class Mul expr a where
  type PreMul expr a

  -- | Multiplication.
  infixl 7 *:                   -- match Haskell's precedence
  (*:) :: expr e (PreMul expr a) -> expr e (PreMul expr a) -> expr e a

-- | Multiplication of (metalanguage) literals to (object language)
-- expressions.

class MulLit expr a where
  infixl 7 >*:
  (>*:) :: a -> expr e a -> expr e a

-- | Symantics for division-by-2 of a known-to-be-even value along
-- with its integer modulus.

class Div2 expr a where
  type PreDiv2 expr a

  -- | Divide a value that is known to be even, along with its integer
  -- modulus, by two.
  div2_ :: expr e (PreDiv2 expr a) -> expr e a
