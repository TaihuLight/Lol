
module Crypto.Alchemy.Language.Pair where

import Crypto.Alchemy.Language.Lambda

class Lambda expr => Pair expr where
  pair_ :: expr e (Arrow expr a (Arrow expr b (a,b)))
