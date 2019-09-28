{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module DTalC where

-- Definitions
newtype Expr f = In (f (Expr f))

-- We define a separate data type for each constructor we want to use
-- then we can combine them together using the (:+:) operator to make
-- our data types à la carte.

newtype Lit a = Lit Int
    deriving Show

data Add a = Add a a
    deriving Show

-- Coproduct
data (f :+: g) e = Inl (f e) | Inr (g e)
    deriving Show

infixr 1 :+:

-- By defining functor instances we can write a generic fold operator
-- which will be useful to evaluate our expressions.

instance Functor Lit where
  fmap _ (Lit a) = Lit a

instance Functor Add where
  fmap f (Add a b) = Add (f a) (f b)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl a) = Inl (fmap f a)
  fmap f (Inr b) = Inr (fmap f b)

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In e) = f (fmap (foldExpr f) e)

-- Now we can write a simple interpreter. Your definitions should correspond
-- closely with the definition for the old interpreter given in the description.

class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Lit where
  evalAlgebra (Lit x) = x

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (Inl l) = evalAlgebra l
  evalAlgebra (Inr r) = evalAlgebra r
  
eval :: Eval f => Expr f -> Int
eval = foldExpr evalAlgebra

-- HINT: Use foldExpr

-- The problem is that it is painful to write expressions. 
-- This is how you would write 5+6

pain :: Expr (Lit :+: Add)
pain = In (Inr (Add (In (Inl (Lit 5))) (In (Inl (Lit 6)))))

-- Injection
-- To ease writing expressions, we will now define a type class
-- which will choose the right constructors for us. Think of the sub :<: sup to say that
-- sub is a subtype of sup. 

-- It might also help to think of :+: as the cons operator for a type level list.
-- Then the type class can be viewed as searching for the correct injection by
-- searching through the list for the correct type.

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a

-- Reflexivity
instance Functor f => f :<: f where
  inj = id

instance (Functor f, Functor g) =>  f :<: (f :+: g) where
  inj = Inl

instance {-# OVERLAPPABLE #-} 
        (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
  
-- Note: This part requires overlapping instances, this is safe as long as :+: associates to the right.
-- A modern implementation would use type families. 

-- Then we can use this type class to write smart constructors.

inject :: (g :<: f) => g (Expr f) -> Expr f
inject = In . inj

lit :: (Lit :<: f) => Int -> Expr f
lit e = inject (Lit e)

add :: (Add :<: f) => Expr f -> Expr f -> Expr f
add e1 e2 = inject (Add e1 e2) 

-- Then as long as we specify the type, writing expressions is easy.

expr :: Expr (Add :+: Lit)
expr = add (lit 5) (lit 6)

-- > eval expr
-- 11

-- We can add multiplication very easily.

data Mult a = Mult a a 
    deriving Functor

instance Eval Mult where
  evalAlgebra (Mult a b) = a * b

mult :: (Mult :<: f) => Expr f -> Expr f -> Expr f
mult e1 e2 = inject (Mult e1 e2)
