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

newtype Lit a = Lit Int
    deriving (Show, Functor)

data Add a = Add a a
    deriving (Show, Functor)

class Summable (fs :: [Type -> Type]) where
    data Summed fs :: Type -> Type

instance Summable '[] where
    data Summed '[] a = SummedNil Void deriving (Functor, Show)

instance Summable (f ': fs) where
    data Summed (f ': fs) a = Functor f => Here (f a)
                            | Elsewhere (Summed fs a)
deriving instance Functor (Summed fs) => Functor (Summed (f ': fs))
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

