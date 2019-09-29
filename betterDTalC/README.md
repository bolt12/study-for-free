## Better Data Types a la Carte

This post presents a variation of DTalC which is type-safe, and contains the missing machinery.

*Author:* Sandy Maguire
*Link:* https://reasonablypolymorphic.com/blog/better-data-types-a-la-carte/

## Notes

### Review of Data Types a la Carte

Sandy Maguire presents, in his RPG generator example, a way to be able "to mix and match 
individual constructors into one larger data structure, which we can then transform as we see fit".
However, Data Types a la Carte isn't as type safe as it should be and has missing
machinery, in particular, the ability to remove constructors from the coproduct.

- Not type safe enough
- Missing machinery (Removing constructors from the coproduct)

The class `:<:` won't find the right injection for any sum tree which isn't right
associative, since it only recurses right.

Sandy defends that if we must adhere to a strict convention in order for things to work it
means that the solution is very bug prone.

### Better Data Types a la Carte

#### Type safe injections

As we stated, the problem with the `:<:` class is that we need to adopt the convention to
only build right associative sum trees. The fun thing is that, right associative sum trees
are isomorphic to lists and we should use that instead! But how? Sandy Maguire's uses type
level black magic to promote term level objects to the type level by using the `{-#
LANGUAGE DataKinds #-}` extension; Sandy also uses `{-# LANGUAGE TypeFamilies #-}` to
write type level functions!

So, the following type class is introduced:

```Haskell
class Summable (fs :: [* -> *]) where
    data Summed fs :: * -> * 
```

Here `fs` is a type as is `Summed fs`, the only difference is that `fs` is a list of types
that look like a Functor and `Summed fs` is a type that looks like one.

Why this type class? This type class will let us define, by induction a way to build a
nested sum type out of a type level list of types! And the best part is that it is right
asassociative crucially, not by convention!

Sandy helps us understand how to perform this magical type level inductive definition:

```Haskell
instance Summable '[] where
    data Summed '[] a = SummedNil Void
                      deriving Functor
```

- The base case
- `'[]` is the type level empty list (because terms were promoted to the type level)
- What should happen if we want to create a sum tree of 0 types? Nothing? Give an error?
  NO! We should... make it impossible to construct, thus the use of Void. Sandy gives a
  good explanation too: "notice that `Either a Void` must be `Left a`, since the Left 
  branch can never be constructed". This is a very nice thing because it implies that
  the compiler will be able to infer the right injection.

```Haskell
instance Summable (f ': fs) where
    data Summed (f ': fs) a = Functor f => Here (f a)
                            | Elsewhere (Summed fs a)

{-# LANGUAGE StandaloneDeriving #-}
deriving instance Functor (Summed fs) => Functor (Summed (f ': fs))
```

- Step case
- `Summed` for a non-empty type level list is either the head of the list (`Here`) or the
  tail (`Elsewhere`).
- For reasons that do not matter (and I don't understand) we need to specify that `Summed` 
  is a functor like that.

This gives us what we want: A data type that builds a nested sum-type from a type level
list of other types.

Now we can define `inj` just like DTalC:

```Haskell
class Injectable (f :: * -> *) (fs :: [* -> *]) where
    inj :: f a -> Summed fs a
```

We need to write instances of `Injectable`:

```Haskell
instance Injectable f (f ': fs) where
    inj = Here

instance (Injectable f fs) => Injectable f (g ': fs) where
    inj = Elsewhere . inj
```

Since we cannot construct `Summed '[]` there is no instance for it.

So now we finally have what Swiestra had in DTalC but without the convention to keep
everything right associative because we fixed it with `Summed`.

#### Outjections

Having improved the machinery needed to inject type constructors, Sandy tries to implement
something that is able to project a type constructor out of the sum tree (Swiestra
mentioned the possibility but never showed an actual implementation).

With this being said Sandy tries to achieve the following:

```Haskell
class Outjectable (f :: * -> *) (fs :: [* -> *]) where
    outj :: Summed fs a -> Maybe (f a)
```

And it happens that, following a very similar approach as `inj`, we can define the
inductive instances to get what we want!

```Haskell
instance Outjectable f (f ': fs) where
    outj (Here fa) = Just fa
    outj (Elsewhere _) = Nothing

instance {-# OVERLAPPABLE #-} Outjectable f fs => Outjectable f (g ': fs) where
    outj (Here _) = Nothing
    outj (Elsewhere fs) = outj fs
```

Beautiful! Sandy proceeds on doing some magic to package all these typeclasses into
something more user friendly by using the following trick:

```Haskell
class ( Summable fs
      , Injectable f fs
      , Outjectable f fs
      , Functor (Summed fs)
      ) => (f :: * -> *) :<: (fs :: [* -> *])
instance ( Summable fs
         , Injectable f fs
         , Outjectable f fs
         , Functor (Summed fs)
         ) => (f :<: fs)
```

#### Playground

If you look in the Haskell file in this folder you'll find an implementation of these type
classes. I went forward and implemented the `Show` instance to be able to see what terms
are being generated and to play with the types a little.

```
> :t inj (Lit 1)
inj (Lit 1) :: Injectable Lit fs => Summed fs a
```

```
> inj (Lit 1) :: (Summed '[Lit] ())
Here (Lit 1)
```

```
> inj (Lit 1) :: (Summed '[Add, Lit] ())
Elsewhere (Here (Lit 1))
```

```
> :t inj (Add (Lit 1) (Lit 2))
inj (Add (Lit 1) (Lit 2)) :: Injectable Add fs => Summed fs (Lit a)
```

```
> inj (Add (Lit 1) (Lit 2)) :: (Summed '[Lit, Add] (Lit a))
Elsewhere (Here (Add (Lit 1) (Lit 2)))
```

```
> inj (Add (Lit 1) (Lit 2)) :: (Summed '[Add, Lit] (Lit a))
Here (Add (Lit 1) (Lit 2))
```

If you're like me and are a little confused on what it means to "outject" a data
constructor look at this:

```
>:t (Here (Lit 1))
Here (Lit 1) :: Summed (Lit : fs) a
>:t outj
outj :: Outjectable f fs => Summed fs a -> Maybe (f a)
>outj (Here (Lit 1))
> outj (Here (Lit 1)) :: Maybe (Lit a)
Just (Lit 1)
```

If we experiment on the Free monadic constructio from DTalC:

*NOTE:* The `Lit` data constructor now needs to have a second argument `a` to carry the
rest of the computation!

```Haskell
> :t (Impure (Here (Lit 1 (Pure 1))))
(Impure (Here (Lit 1 (Pure 1))))
  :: Num a => Term (Summed (Lit : fs)) a
> :t program
program
  :: (Summable f, Functor (Summed f), Injectable Lit f,
      Injectable Add f, Outjectable Lit f, Outjectable Add f) =>
     Term (Summed f) Int
```

The order of the type list makes difference but the compiler is able to infer everything:

```
> (program :: Term (Summed [Add, Lit]) Int)
Impure (Elsewhere (Here (Lit 1 (Impure (Elsewhere (Here (Lit 2 (Impure (Here (Add (Impure (Elsewhere (Here (Lit 1 (Pure 2))))) (Impure (Elsewhere (Here (Lit 2 (Pure 4)))))))))))))))
> (program :: Term (Summed [Lit, Add]) Int)
Impure (Here (Lit 1 (Impure (Here (Lit 2 (Impure (Elsewhere (Here (Add (Impure (Here (Lit 1 (Pure 2)))) (Impure (Here (Lit 2 (Pure 4)))))))))))))
```

*NOTE:* The leafs of the tree actually contain the last computation to be made!

Extracting `Lit`: 

```
> outTerm (Impure p) = out p
> :t outTerm
outTerm
  :: Outjectable f fs =>
     Term (Summed fs) a -> Maybe (f (Term (Summed fs) a))
```

```
> outTerm (program :: Term (Summed [Add, Lit]) Int) :: Maybe (Lit (Term (Summed '[Add, Lit]) Int))
Just (Lit 1 (Impure (Elsewhere (Here (Lit 2 (Impure (Here (Add (Impure (Elsewhere (Here (Lit 1 (Pure 2))))) (Impure (Elsewhere (Here (Lit 2 (Pure 4)))))))))))))
```

If we try to get `Add`: 

```
outTerm (program :: Term (Summed [Add, Lit]) Int) :: Maybe (Add (Term (Summed '[Add, Lit]) Int))
Nothing
```

This happens because `outTerm` only provides the first layer of the `Term` type to `outj`
and since it cannot find any `Add` constructors it returns `Nothing`. Nonetheless this
gives a pretty nice intuition on how we are able to get all the constructors for a given
type in a program and do something with them!


### References

- https://reasonablypolymorphic.com/blog/better-data-types-a-la-carte/
