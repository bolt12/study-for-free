{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}

module Main where

import Prelude hiding (abs, getChar, putChar)
import qualified Prelude as P
import Control.Monad (when)

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

abs :: Monad m => C m a -> m a 
abs (C p) = p return

rep :: Monad m => m a -> C m a 
rep m = C (m >>=)

instance Functor (C m) where
    fmap f (C m) = C (\a -> m (a . f))

instance Applicative (C m) where
    pure a = C (\x -> x a)
    (C f) <*> (C a) = C (\bb1 -> f (\ab -> a (bb1 . ab)))

instance Monad (C m) where
    return = pure
    (C m) >>= f = C (\bb1 -> m (\a -> case f a of (C m') -> m' bb1))

class (Functor f, Monad m) => FreeLike f m where
    wrap :: f (m a) -> m a


instance Functor f => FreeLike f (Free f) where
    wrap = Wrap

instance (FreeLike f m) => FreeLike f (C m) where
    wrap fcfa = C (\afb -> wrap (fmap (\(C p) -> p afb) fcfa))

improve :: Functor f => (forall m . FreeLike f m => m a) -> Free f a
improve = abs

--

data F_IO f = GetChar (Char -> f)
            | PutChar Char f
            deriving (Functor)

getChar :: FreeLike F_IO m => m Char
getChar = wrap (GetChar return)

putChar :: FreeLike F_IO m => Char -> m ()
putChar c = wrap (PutChar c (return ()))

program :: FreeLike F_IO m => m ()
program = do
    c <- getChar 
    when (c /= ' ') $ do
        program
        putChar c

run :: Free F_IO a -> IO a
run (Return a) = return a
run (Wrap (GetChar f)) = P.getChar >>= run . f
run (Wrap (PutChar c f)) = P.putChar c >> run f

main :: IO ()
main = run program

{- Improved version
main :: IO ()
main = run (improve program)
-}
