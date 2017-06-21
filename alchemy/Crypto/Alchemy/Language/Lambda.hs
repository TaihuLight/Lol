{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.Lambda where

-- | Symantics for functions and application.

class Lambda expr where
  -- | Representation of an object-language function from @a@ to @b@.
  data Arrow expr a b

  -- | Lambda abstraction.
  lam :: expr (e,a) b -> expr e (Arrow expr a b)

  -- | Application.
  infixl 1 $:             -- ($) is infixr, but l is nicer for obj lang
  ($:) :: expr e (Arrow expr a b) -> expr e a -> expr e b

  -- | The zero'th (most-recently bound) variable.
  v0 :: expr (b,a) a

  -- | Extend environment.
  s  :: expr e a -> expr (e,x) a

-- | Let-sharing.
let_ :: Lambda expr => expr e a -> expr (e,a) b -> expr e b
let_ a f = lam f $: a

-- | Object-language function composition.
comp_ :: Lambda expr =>
  expr e (Arrow expr (Arrow expr b c)
          (Arrow expr (Arrow expr a b) (Arrow expr a c)))
comp_ = lam $ lam $ lam $ v2 $: (v1 $: v0)

infixr 9 .:
-- | Convenient metalanguage version of '(.:)'.
(.:) :: (Lambda expr) =>
        expr e (Arrow expr b c)
     -> expr e (Arrow expr a b)
     -> expr e (Arrow expr a c)
f .: g = comp_ $: f $: g

-- CJP: for some reason have to give signature here, even though ghci
-- infers them correctly

-- | The one'th (second-most-recently bound) variable.
v1 :: Lambda expr => expr ((c,b),a) b
v1 = s v0

v2 :: Lambda expr => expr (((d,c),b),a) c
v2 = s v1

v3 :: Lambda expr => expr ((((e,d),c),b),a) d
v3 = s v2

v4 :: Lambda expr => expr (((((f,e),d),c),b),a) e
v4 = s v3
