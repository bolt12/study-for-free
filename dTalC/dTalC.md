## Data Types à la Carte

This paper describes a technique for assembling both data types and functions from isolated
individual components. We also explore how the same technology can be used to combine
free monads and, as a result, structure Haskell’s monolithic IO monad.

*Author:* Wouter Swiestra
*Link:* https://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf

## Notes

### Answer to the Expression Problem

Swiestra gives a response to the 'Expression Problem' where "The key idea is to combine
different expressions by using the coproduct of their signatures". Given this we cannot
have the expression signatures fixed to some data structure as you would do it in BNF
form, instead you use the following type:

```Haskell
data Expr f = In (f (Expr f))
```

Where `f` is the signature of the constructors. So if we want expressions that
consisted only on integers we'd write the following:

```Haskell
data Val e = Val Int

type ValExpr = Expr Val
```

Since `Val` doesn't use it's type parameter `e` the only expression we can build is in the
form `In (Val x)`.

A more complex one would be the expression that consists only on addition:

```Haskell
data Add e = Add e e

type AddExpr = Expr Add
```

So how could we build expressions consisting on a combination of `Val` and `Add`?

Swiestra gives an answer to this question by saying that we could combine this two types
by using the coproduct:

```Haskell
data (f :+: g) e = InL (f e) | InR (g e)

-- The combination of the two types (Val & Add)
addExample :: Expr (Val :+: Add)
addExample = In (Inr (Add (In (Inl (Val 118))) (In (Inl (Val 1219)))))
```

As we can see we were able to combine the two types and build an expression that is
isomorphic to the version with the constructors fixed:

```Haskell
data Expr = Val Int | Add Expr Expr

addExample' :: Expr
addExample = Add (Val 118) (Val 1219)
```

Although we were able to combine the two types and build a more powerful expression, it is
painful to write the expression itself. Furthermore, it doesn't scale well if we want to 
add more types since we'll have to update any values written because the injections
might not be right.

### How to Evaluate expressions

The first step to evaluate expressions is to define the Functor instances of the types to
be combined.

```Haskell
instance Functor Val where
    fmap f (Val x) = Val x

instance Functor Add where
    fmap f (Add e1 e2) = Add (f e1) (f e2)
```

Furthermore the coproduct of two functors is a functor too (Bifunctor):

```Haskell
instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (InL e) = InL (f e)
    fmap f (InR e) = InR (f e)
```

These instances are important because they let us fold over any value of type `Expr f`, if
`f` is a Functor:

```Haskell
foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr g (In t) = g (fmap (foldExpr g) t)
```

The type `f a -> a` is known as a F-Algebra and using Haskell’s type system we can write
one F-Algebra in a modular fashion.

```Haskell
class Functor f => Eval f where
    evalAlgebra :: f Int -> Int
```

The class `Eval` constraints the result to be of type `Int` and in the case of the `Add`
type the variables `x` and `y` are the result of the recursive calls.

```Haskell
instance Eval Val where
    evalAlgebra (Val x) = x

instance Eval Add where
    evalAlgebra (Add x y) = x + y

instance Eval (f :+: g) where
    evalAlgebra (InL f) = evalAlgebra f
    evalAlgebra (InR g) = evalAlgebra g

eval :: Eval f => Expr f -> Int
eval = foldExpr evalAlgebra
```

```
> eval addExample
1337
```

### Automating Injections

So far we are able to:

- Obtain more complex expressions by combining primitive type signatures
- Evaluate in a modular fashion any expression

But it is still impracticable to write expressions like `addExample` because of the
troublesome overhead that it's included... Fortunately, Swiestra's gives an answer to this
problem and presents a way to automate most of the boilerplate introduced by the
coproducts.

A first attempt at automating the writing of an expression would be:

```Haskell
val :: Int -> Expr Val
val x = In (Val x)

add :: Expr Add -> Expr Add -> Expr Add
add e1 e2 = In (Add e1 e2)
```

But writing `add (val 1) (val 2)` gives a type error because `Expr Val` and `Expr Add` are
two different types!

We need a smart constructor that can figure out the right injection to use!

```Haskell
add :: (Add :<: f ) => Expr f -> Expr f -> Expr f
val :: (Val :<: f ) => Int -> Expr f
```

You may want to read the type constraint `Add :<: f` as "any signature f that
supports addition."

The constraint `sub :<: sup` should only be satisfied if it is possible to inject 'sub'
into 'sup'. Swiestra proposes the following type class:

```Haskell
class (Funcor sub, Functor sup) => sub :<: sup where
    inj :: sub a -> sup a
```

This class only has 3 instances which define an inductive way of figuring out which
injection to do!

```Haskell
instance Functor f => f :<: f where
    inj = id

instance (Functor f, Functor g) => f :<: (f :+: g) where
    inj = Inl

instance (Functor f, Functor g, Functor h, f :<: g) ⇒ f :<: (h :+: g) where
    inj = Inr . inj
```

- The first one says "if there’s nowhere left to go, we’re here!"
- The second says "if our desired functor is on the left, use InL!"
- The third says "If our desired functor can be injected in 'g', then inject it in 'g' and
  put it on the right with InR!"

Given this we can use this type class to define our smart constructors:

```Haskell
inject :: (g :<: f) => g (Expr f) -> Expr f
inject = In . inj

val :: (Val :<: f) => Int -> Expr f
val x = inject (Val x)

add :: (Add :<: f) ⇒ Expr f -> Expr f -> Expr f
add x y = inject (Add x y)
```

```
> let x :: Expr (Add :+: Val ) = add (val 30000) (add (val 1330) (val 7))
> eval x
31337
```

#### NOTE

If you're like me and bugged out on the type of `inject` and don't know what the
hell `g (Expr f)` is supposed to mean and how the hell `inject (Val 1)` works when `Val 1
:: Val a`, I will explain:

`g :<: f` seems to be "g is subtype of f" as in "I can transform `g a` into `f a`". So, 
`inject` works because when you know you can turn `g` into `f`, you can use 
`In :: f (Expr f) -> Expr f` on `inject :: g a -> f a` to make `g (Expr f)` into `Expr f`

More intuitively, what you want is to automate the injection and get an `Expr f` out of a
type constructor like `Val` or `Add`. So, the objective is to at least have a funtion
which the final result is of type `Expr f`:

- Final type: `Expr f`
- Function type: `inject :: _ -> Expr f`
- Function implementation: `inject = _`

Taking a look on how we can construct an expression for `Expr (Val :+: Add)`:
`In (Inl (Val 1))`; we see that we first need to get the injection right and since there's
only one function that allows us to do that we have no other choice but to use `inj ::
(sub :<: sup) => sub a -> sup a`.

- Final type: `Expr f`
- Function type: `inject :: (sub :<: sup) => sup a -> Expr f`
- Function implementation: `inject = _ . inj`

In the function implementation we used `inj` and consequently the type definition changed
because we now want to get an `Expr f` out of the result of `inj` which is of type `sup
a`. Since there's only one way to construct things of type `Expr f` we use that (`In :: f
(Expr f) -> Expr`).

- Final type: `Expr f`
- Function type: `inject :: (sub :<: f) => f (Expr f) -> Expr f`
- Function implementation: `inject = In . inj`

Finally we have the same implementation as Swiestra but the types still cause some
confusion! Since we want the final type to be `Expr f` and the only way to get `Expr f` is
by calling `In` then, `sup a ~ f (Expr f)` which means that `sup ~ f` and `a ~ Expr f`!

Imagine we are instanciating for `Expr (Val :+: Add)` and calling `inject (Val
1)`, in this case `sup` functor above needs to be `(Val :+: Add)` since we can inject
`Val` into `Val :+: Add` and, since `a` is polymorphic, it can be `Expr f`.

### Monads for Free

Monads are very famous in the functional programming world. They provide a very good
abstraction for computations and Haskell uses Monads to encapsulate side effects such as
IO.

The problem with monads is that they do not compose, i.e. are very hard to combine. If one
wants to run a computation inside the State Monad that needs to access IO it is not
possible to do so without recurring to heavy machinery.

Free Monads is a construction that, provided a Functor it gives a Monad back:

```Haskell
data Term f a = Pure a | Impure (f (Term f a))
```

Where `Pure a` represents a pure value computation and `Impure` an impure computation. 
If we substitute `Impure` by `Expr` on the right we can see some similarities with the
`Expr` type defined above!

Since Data Types a la Carte is all about defining type signatures that can be combined to
create more complex expressions by using coproducts one could try and take advantage of
the same technique to define monads modularly!

By using Monads in Haskell we have access to the `do` notation and we're able to build
sequential programs for Free. All we need to do is to incrementally construct these
terms and interpret them as computations in whatever monad we wish!

And what do we gain by combining Monads modularly? In Haskell, in particular, the IO
monad has evolved into a ‘sin bin’ that encapsulates every kind of side effect from
addFinalizer to zeroMemory. With the technology presented in the previous sections,
we can be much more specific about what kind of effects certain expressions may
have. For instance:

```Haskell
data Teletype a =
    GetChar (Char -> a)
    | PutChar Char a
data FileSystem a =
    ReadFile FilePath (String -> a)
    | WriteFile FilePath String a
```

We can execute terms constructed using these types by calling the corresponding
primitive functions from the Haskell Prelude. To do so, we define a function `exec`
that takes pure terms to their corresponding impure programs.

```Haskell
exec :: Exec f => Term f a -> IO a
exec = foldTerm return execAlgebra
    where
        foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Term f a -> b
        foldTerm = ...
```

Assuming the Functor instances and the type class instances are implemented we can use the
smart constructors defined before (with only a slight change) to write pseudo-IO programs:

```Haskell
cat :: FilePath => Term (Teletype :+: FileSystem) ()
cat fp = do
    contents ← readFile fp
    mapM putChar contents
    return ()
```

*NOTE:* The type signature of `cat` could be as follows 
`(Teletype :<: f, FileSystem :<: f) => FilePath => Term f ()` and there is a clear choice
here. We could choose to let `cat` work in any `Term` that
supports these two operations; or we could want to explicitly state that `cat` should
only work in the `Term (Teletype :+: FileSystem)` monad.

Now the type of `cat` tells us exactly what kind of effects it uses: a much healthier
situation than a *single monolithic* IO monad. For example, our types guarantee
that executing a term in the `Term Teletype` monad will not overwrite any files on
our hard disk. Other very good advantages of using this technique is that we can define
pure interpretation in order to test if the behaviour of the program logic is correct
without the need to setup a whole new testing dedicated project, and the fact that we can
reutilize the effects in a modular fashion!

### References

- https://reasonablypolymorphic.com/blog/better-data-types-a-la-carte/
- https://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf
