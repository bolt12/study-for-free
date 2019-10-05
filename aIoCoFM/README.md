## Asymptotic Improvement of Computations over Free Monads

We present a low-effort program transformation to improve
the efficiency of computations over free monads in Haskell. The develop-
ment is calculational and carried out in a generic setting, thus applying
to a variety of datatypes. An important aspect of our approach is the
utilisation of type class mechanisms to make the transformation as trans-
parent as possible, requiring no restructuring of code at all. There is also
no extra support necessary from the compiler (apart from an up-to-date
type checker). Despite this simplicity of use, our technique is able to
achieve true asymptotic runtime improvements. We demonstrate this by
examples for which the complexity is reduced from quadratic to linear.

*Author:* Janis Voigtlander

*Link:* https://www.janis-voigtlaender.eu/papers/AsymptoticImprovementOfComputationsOverFreeMonads.pdf

## Notes

## Difference List

In the first section, Janis gives a motivating example for the problem at hands and
concludes that we can create an alternative representation of trees somewhat akin to the
"novel representation of lists" of Hughes to gain an asymptotic improvement.

Hughes, proposes a representation of lists as first-class functions. Lists represented
this way can be appended together in constant time and be converted back to an ordinary
list in time proportional to their length.

After reading this last paragraph you might be wondering how is that possible. And the
truth is every programmer as stumble upon the inneficiency of using the function that
appends two lists in their code.

```Haskell
(++) :: [a] -> [a] -> [a]
[] ++ l = l
(h:t) ++ l = h : (t ++ l)
```

As you can see `(++)` traverses its first argument which leads to left associative appends
to repeatadly traverse the intermediate lists:

- Left associative append = `((a ++ b) ++ c) ++ d`
- Right associative append = `a ++ (b ++ (c ++ d))`

The left associative append traverses `a`, then `a ++ b`, then `(a ++ b) ++ c`.


The right associative append traverses `a`, then `b`, then `c`.

So, in order to optimize this we just need to try and force computations to be right
associative!

What Hughes proposes is a new representation for lists! And for this representation to be
valid it needs to define two functions:

```Haskell
abs :: R -> A
rep :: A -> R
```

The funtion `rep` converts an abstract object into its representation, and the function
`abs` recovers the abstract object from the representation. And the following law must
hold:

```Haskell
abs . rep = id
```

Now suppose that `f :: A -> A` is an operation on abstract objects which must be
implemented on representations. It is required that a function `g :: R -> R` which
'implements' `f` in some sense. This sense can be made precise by referring to `abs` and
`rep`. `g` implements `f` iff `f . abs = abs . g`. This law can be used to prove
correctness.

Given this, in order to implement a correct representation for lists we need to respect
the former. Hughes proposes representing lists as functions from lists to lists (`[a] ->
[a]`), given this:

```Haskell
rep l = (++) l
abs f = f []
```

_NOTE:_ Proof that this representation is correct can be found in Hughes paper.

This representation is interesting because two representations can be appended together by
composing them as functions:

```Haskell
appendR f g = f . g

appendR (rep l1) (rep l2) h ==
(rep l1 . rep l2) h ==
rep l1 (rep l2 h) ==
l1 ++ (l2 ++ h) ==
(l1 ++ l2) ++ h ==
rep (l1 ++ l2) h
```

Therefore: `appendR (rep l1) (rep l2) = rep (l1 ++ l2)`

We can also deduce: `abs (appendR f g) = (abs f) ++ (abs g)`

Function composition is an efficient operation. It can always be performed in constant
time. For a more thourough explanation on the reverse check this [post](http://h2.jaguarpaw.co.uk/posts/demystifying-dlist/)

### The Generic Setting

Janis, provides a non intrusive technique that deals with a variety of datatypes in one
stroke. With this being said, Janis uses the same technique as Hughes to achieve an
asymptotically better runtime for free monads and suggests a non intrusive technique that
makes already written code faster without requiring restructuring.

Janis provides proof that the representation chosen is valid and the type classes needed
to make the program transformation smooth.

The gist of it stands in the "magic function":

```Haskell
improve :: Functor f => (forall μ . FreeLike f μ => μ a) -> Free f a
improve m = abs m
```

that, once proved the relations
between the representation and abstraction of the datatypes and the equivalence of the
overloaded methods, puts stronger requirements on its argument `m` and that is what 
enables to establish the correctness of adding `improve` at will wherever the 
type checker allows doing so.

### References

- https://www.janis-voigtlaender.eu/papers/AsymptoticImprovementOfComputationsOverFreeMonads.pdf
- https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/lists.pdf
