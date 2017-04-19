{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonoLocalBinds #-} -- required for the LambdaD instance

module Crypto.Alchemy.Interpreter.DupPT where

import Control.Monad.Identity

import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Depth

dupPTM :: (Functor m1, Functor m2) => Identity (Dup m1 expr1 m2 expr2 d a) -> (m1 (expr1 d a), m2 (expr2 d a))
dupPTM d = (unDupA $ runIdentity d, unDupB $ runIdentity d)

--dupPT :: Dup expr1 expr2 d a -> (expr1 d a, expr2 d a)
--dupPT (Dup a b) = (a, b)

data Dup m1 expr1 m2 expr2 (d :: Depth) a = Dup {unDupA :: m1 (expr1 d a), unDupB :: m2 (expr2 d a)}

unpackDup :: (Functor i, Functor j) => (i :. j) (Dup m1 expr1 m2 expr2 d a) -> ((i :. (j :. m1)) (expr1 d a), (i :. (j :. m2)) (expr2 d a))
unpackDup d = (J $ J <$> (unJ $ unDupA <$> d), J $ J <$> (unJ $ unDupB <$> d))

packDup :: (Applicative i, Applicative j) => (i :. (j :. m1)) (expr1 d a) -> (i :. (j :. m2)) (expr2 d a) -> (i :. j) (Dup m1 expr1 m2 expr2 d a)
packDup da db =
  let da' = J $ unJ <$> unJ da
      db' = J $ unJ <$> unJ db
  in Dup <$> da' <*> db'

instance (AddPT expr1, AddPT expr2, Applicative m1, Applicative m2) => AddPT (Dup m1 expr1 m2 expr2) where
  type AddPubCtxPT   i (Dup m1 expr1 m2 expr2) d a = (AddPubCtxPT   i expr1 d a, AddPubCtxPT   i expr2 d a, Applicative i)
  type MulPubCtxPT   i (Dup m1 expr1 m2 expr2) d a = (MulPubCtxPT   i expr1 d a, MulPubCtxPT   i expr2 d a, Applicative i)
  type AdditiveCtxPT i (Dup m1 expr1 m2 expr2) d a = (AdditiveCtxPT i expr1 d a, AdditiveCtxPT i expr2 d a, Applicative i)

{-
d :: (i :. j) (Dup e1 e2 a)
unDupA <$> d :: (i :. j) (m1 (e1 a))
unJ $ unDupA <$> d :: (i (j (m1 (e1 a))))
J <$> _ :: i ((j :. m1) (e1 a))
J $ _ :: (i :. (j :. m1)) (e1 a)


negPT $ _ :: (i :. (j :. m1)) (e1 a)



unJ $ _ :: (i :. j) (m1 (e1 a))
-}
  --da +# db = Dup <$> ((unDupA <$> da) +# (unDupA <$> db)) <*> ((unDupB <$> da) +# (unDupB <$> db))
  negPT d =
    let (da, db) = unpackDup d
    in packDup (negPT da) (negPT db)
  --addPublicPT a db = Dup <$> (addPublicPT a $ unDupA <$> db) <*> (addPublicPT a $ unDupB <$> db)
  --mulPublicPT a db = Dup <$> (mulPublicPT a <$> (J $ unDupA <$> db)) <*> (mulPublicPT a <$> unDupB <$> db)
{-
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
-}