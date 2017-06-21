{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.Arithmetic where

import Crypto.Alchemy.Language.Lambda

-- | Addition.

class (Lambda expr) => Add expr a where
  -- | Addition.
  add_ :: expr e (Arrow expr a (Arrow expr a a))
  -- | Negation.
  neg_ :: expr e (Arrow expr a a)

infixl 6 +:, -:
(+:), (-:) :: (Add expr a) => expr e a -> expr e a -> expr e a

-- | Convenient metalanguage version of 'add_'.
a +: b = add_ $: a $: b

-- | Convenient metalanguage version of subtraction.
a -: b = a +: (neg_ $: b)

-- | Addition of (metalanguage) literals to (object language)
-- expressions.

class (Lambda expr) => AddLit expr a where
  addLit_ :: a -> expr e (Arrow expr a a)

infixl 6 >+:
(>+:) :: (AddLit expr a) => a -> expr e a -> expr e a
a >+: b = addLit_ a $: b

-- | Multiplication. (Note that the input type @b@ may differ from the
-- output type @a@.)

class (Lambda expr) => Mul expr a where
  type PreMul expr a

  -- | Multiplication.
  mul_ :: expr e (Arrow expr (PreMul expr a) (Arrow expr (PreMul expr a) a))

-- | Convenient metalanguage version of 'mul'.
infixl 7 *:                     -- match Haskell's precedence
(*:) :: (Mul expr a) =>
        expr e (PreMul expr a) -> expr e (PreMul expr a) -> expr e a
a *: b = mul_ $: a $: b

-- | Multiplication of (metalanguage) literals to (object language)
-- expressions.

class (Lambda expr) => MulLit expr a where
  mulLit_ :: a -> expr e (Arrow expr a a)

infixl 7 >*:
(>*:) :: (MulLit expr a) => a -> expr e a -> expr e a
a >*: b = mulLit_ a $: b

-- | Symantics for division-by-2 of a known-to-be-even value along
-- with its integer modulus.

class Div2 expr a where
  type PreDiv2 expr a

  -- | Divide a value that is known to be even, along with its integer
  -- modulus, by two.
  div2_ :: expr e (Arrow expr (PreDiv2 expr a) a)
