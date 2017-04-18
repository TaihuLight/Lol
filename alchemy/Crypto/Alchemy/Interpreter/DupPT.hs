{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonoLocalBinds #-} -- required for the LambdaD instance

module Crypto.Alchemy.Interpreter.DupPT where

import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Depth

dupPT :: (Applicative ma, Applicative mb, Applicative i) =>
  (forall m . (Applicative m) => (m :. i) (Dup expr1 expr2 d a))
    -> ((ma :. i) (expr1 d a), (mb :. i) (expr2 d a))
dupPT d = (unDupA <$> d, unDupB <$> d)

data Dup expr1 expr2 (d :: Depth) a = Dup {unDupA :: expr1 d a, unDupB :: expr2 d a}

instance (AddPT expr1, AddPT expr2) => AddPT (Dup expr1 expr2) where
  type AddPubCtxPT   i (Dup expr1 expr2) d a = (AddPubCtxPT   i expr1 d a, AddPubCtxPT   i expr2 d a, Applicative i)
  type MulPubCtxPT   i (Dup expr1 expr2) d a = (MulPubCtxPT   i expr1 d a, MulPubCtxPT   i expr2 d a, Applicative i)
  type AdditiveCtxPT i (Dup expr1 expr2) d a = (AdditiveCtxPT i expr1 d a, AdditiveCtxPT i expr2 d a, Applicative i)

  da +# db = Dup <$> ((unDupA <$> da) +# (unDupA <$> db)) <*> ((unDupB <$> da) +# (unDupB <$> db))
  negPT d = Dup <$> (negPT $ unDupA <$> d) <*> (negPT $ unDupB <$> d)
  addPublicPT a db = Dup <$> (addPublicPT a $ unDupA <$> db) <*> (addPublicPT a $ unDupB <$> db)
  mulPublicPT a db = Dup <$> (mulPublicPT a $ unDupA <$> db) <*> (mulPublicPT a $ unDupB <$> db)

instance (MulPT expr1, MulPT expr2) => MulPT (Dup expr1 expr2) where

  type RingCtxPT i (Dup expr1 expr2) d a = (RingCtxPT i expr1 d a, RingCtxPT i expr2 d a, Applicative i)

  da *# db = Dup <$> ((unDupA <$> da) *# (unDupA <$> db)) <*> ((unDupB <$> da) *# (unDupB <$> db))

instance (LambdaD expr1, LambdaD expr2) => LambdaD (Dup expr1 expr2) where
  lamD f =
    let fa x = unDupA <$> f (flip Dup undefined <$> x)
        fb x = unDupB <$> f (Dup undefined <$> x)
    in Dup <$> (lamD fa) <*> (lamD fb)

  appD fd d =
    let fa = unDupA <$> fd
        fb = unDupB <$> fd
        a = unDupA <$> d
        b = unDupB <$> d
    in Dup <$> (appD fa a) <*> (appD fb b)

instance (Lit (expr1 d), Lit (expr2 d)) => Lit (Dup expr1 expr2 d) where
  type LitCtx (Dup expr1 expr2 d) a = (LitCtx (expr1 d) a, LitCtx (expr2 d) a)
  lit a = Dup (lit a) (lit a)
