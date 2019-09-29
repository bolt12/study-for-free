{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module BetterDTalC where

import Data.Kind (Type)
import Data.Void

data Lit a = Lit Int a
    deriving (Show, Functor)

data Add a = Add a a
    deriving (Show, Functor)

data Term f a = Pure a | Impure (f (Term f a))

deriving instance (Show a, Show (f (Term f a))) => Show (Term f a)

instance (Functor f) => Functor (Term f) where
    fmap f (Pure a) = Pure (f a)
    fmap f (Impure fm) = Impure (fmap (fmap f) fm)

instance (Functor f) => Applicative (Term f) where
    pure = Pure 
    Pure a <*> Pure b = Pure $ a b
    Pure a <*> Impure mb = Impure $ fmap a <$> mb
    Impure ma <*> b = Impure $ (<*> b) <$> ma

instance (Functor f) => Monad (Term f) where
    return = Pure
    (Pure x) >>= f = f x
    (Impure t) >>= f = Impure (fmap (>>= f) t)

inject :: (g :<: f) => g (Term (Summed f) a) -> Term (Summed f) a 
inject= Impure . inj

lit :: (Lit :<: f) => Int -> Term (Summed f) Int
lit x = inject (Lit x (Pure x))

add :: (Add :<: f) => Term (Summed f) Int -> Term (Summed f) Int -> Term (Summed f) Int
add x y = inject (Add x y)

program :: (Lit :<: f, Add :<: f) => Term (Summed f) Int
program = do
    x <- lit 1
    y <- lit 2
    z <- add (lit 1) (lit 2)
    return (x * y * z)

class Summable (fs :: [Type -> Type]) where
    data Summed fs :: Type -> Type

instance Summable '[] where
    data Summed '[] a = SummedNil Void deriving (Functor, Show, Foldable)

instance Summable (f ': fs) where
    data Summed (f ': fs) a = Functor f => Here (f a)
                            | Elsewhere (Summed fs a)
deriving instance Functor (Summed fs) => Functor (Summed (f ': fs))
deriving instance (Foldable f, Foldable (Summed fs)) => Foldable (Summed (f ': fs))
deriving instance (Show (f a), Show (Summed fs a)) => Show (Summed (f ': fs) a)

class Injectable (f :: Type -> Type) (fs :: [Type -> Type]) where
    inj :: f a -> Summed fs a

instance Functor f => Injectable f (f ': fs) where
    inj = Here

instance {-# OVERLAPPABLE #-} Injectable f fs => Injectable f (g ': fs) where
    inj = Elsewhere . inj

class Outjectable (f :: Type -> Type) (fs :: [Type -> Type]) where
    outj :: Summed fs a -> Maybe (f a)

instance Outjectable f (f ': fs) where
    outj (Here f)      = Just f
    outj (Elsewhere _) = Nothing

instance {-# OVERLAPPABLE #-} Outjectable f fs => Outjectable f (g ': fs) where
    outj (Here _ )     = Nothing
    outj (Elsewhere f) = outj f

class ( Summable fs
      , Injectable f fs
      , Outjectable f fs
      , Functor (Summed fs)
      ) => (f :: Type -> Type) :<: (fs :: [Type -> Type])
instance ( Summable fs
         , Injectable f fs
         , Outjectable f fs
         , Functor (Summed fs)
         ) => (f :<: fs)

