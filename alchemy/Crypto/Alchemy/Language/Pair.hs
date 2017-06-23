
module Crypto.Alchemy.Language.Pair where

class Pair expr where
  pair_ :: expr e a -> expr e b -> expr e (a,b)
