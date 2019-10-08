{-# LANGUAGE Rank2Types #-}

module AIoCoFM where

data Free f a = Return a
              | Wrap (f (Free f a))

instance Functor f => Functor (Free f) where
    fmap f (Return a) = Return (f a)
    fmap f (Wrap x) = Wrap (fmap (fmap f) x)

instance Functor f => Applicative (Free f) where
    pure = Return 
    (Return f) <*> (Return a) = Return (f a)
    (Return f) <*> (Wrap x) = Wrap (fmap (fmap f) x)
    (Wrap f) <*> b = Wrap (fmap (<*> b) f)

instance Functor f => Monad (Free f) where
    return = Return
    (Return a) >>= f = f a
    (Wrap t) >>= f = Wrap (fmap (>>= f) t)

--
        
newtype C m a = C (forall b . (a -> m b) -> m b)

abs' :: Monad m => C m a -> m a 
abs' (C p) = p return

rep' :: Monad m => m a -> C m a 
rep' m = C (m >>=)

instance Functor (C m) where
    fmap f (C m) = C (\a -> m (a . f))

instance Applicative (C m) where
    pure a = C (\x -> x a)
    (C f) <*> (C a) = C (\bb1 -> f (\ab -> a (bb1 . ab)))

instance Monad (C m) where
    return = pure
    (C m) >>= f = C (\bb1 -> m (\a -> case f a of (C m') -> m' bb1))
