---
title: Verifying the Titular Properties of a Leftist Heap
postType: Technical
inWhich: my job search leads me to verify the titular properties of a leftist
  heap using Haskell's type-level features and to test it by way of simulation
  using QuickCheck. We also cover much of Haskell's type-level computation
  features from scratch.
published: false
---

## The story

I've made it to the final stage of my computer science PhD, you know the one
where you start looking for jobs, get yourself a copy of [Cracking the Coding
Interview](https://amzn.to/2Q74ckU) (affiliate link), and realise that you
haven't done much of the kind of programming that about half of the companies
expect you to do at their job interviews (and at their job interviews only).

At some point in the book, it says "know how to implement these data structures
by heart: dynamically sized arrays, hash tables, [...], **binary heaps**,
[...]". It dawned on me that I remember the heap property and the heap
interface, but not how to implement it. I was horrified when I remembered
despite conceptually being a tree, binary heaps are implemented using arrays.
Despite having used Haskell as my primary language, decided to implement it in
Ruby---my prior primary language. Some time and indexing errors later, I got it
working.  Then ported it to Haskell's using the [`ST`
monad](http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Monad-ST.html).
After writing `STRef`{.haskell} one too many times, I got that working too, but
it left much to be desired. "Save the trees" yelled my terminal!

Finally, I consulted Dr Chris Okasaki's [Purely Functional Data
Structures](https://amzn.to/34ICTAM) (affiliate link). A leftist heap is one of
the first data structures discussed in the book. It has better worst-case
asymptotic complexity than the binary heap, is represented as
a tree, and doesn't need mutation. Great! I was pleased to have a heap under my
belt that was much easier to remember and much more difficult to get its
implementation wrong.

Staring at it for a while (and being bored while trying to find various
substrings with various properties in linear time and constant space under an
hour over the phone), I got a burning desire to encode the titular properties
of a leftist heap using fancy types. Having listened to hundreds of people
complain about the state of type-level programming in Haskell, I found the
process to be rough around the edges, but functional (see what I did there) that
I wanted to share it.

## The spiel

This brings us to the post at hand. This post is a bit long, but the upside is
there is something for everybody. Hopefully, some of the following piques your
interest:

 - leftist heaps as a purely functional alternative to array-based binary heaps,
 - complexity analysis of operations on leftist heaps,
 - a case study on the internalist approach to verifying data structures,
 - a tutorial on most major features of type-level programming in Haskell,
 - a commentary on the ergonomics of verification using fancy types in Haskell,
 - and practical advice on avoiding pitfalls when using fancy types.

Beginners beware! Type-level programming can be daunting. It certainly was for
me for a long time. I'll attempt to explain fancy types from scratch. If you
find yourself getting confused, it's almost certainly my fault. Just let me know
(contact details on my [homepage](/)) and I'll clarify the post.

## The itinerary

Here are the sections and what to expect from them.

 - [A simple heap](#a-simple-heap) covers the generic heap interface through a
   typeclass and a trivial instance for it. Type-level features: associated type
   families;
 - [A leftist heap](#a-leftist-heap) describes a data type for leftist heaps
   without using fancy types and discusses the asymptotic complexities of its
   operations;
 - [Terms, types, and kinds](#terms-types-and-kinds) covers the basic entities
   in modern Haskell and how they relate to each other. Type-level features:
   [data type promotion](#data-type-promotion), [kind
   polymorphism](#kind-polymorphism), and
   [levity-polymorphism](#levity-polymorphism);
 - [Verifying the leftist property](#verifying-the-leftist-property) explains
   the data type encoding the leftist property and the implementation of its
   property preserving operations. Type-level features: [generalised algebraic
   data types](#generalised-algebraic-data-types),
   [singletons](#singletons-faking-dependent-types), kind signatures through the
   example of [natural numbers](#natural-numbers), and existential types through
   [the heap instance for our data type](#heap-instance-for-safeheap). We also
   introduce [theorem proving](#comparing-without-forgetting) in Haskell.
 - [Verifying the heap property](#verifying-the-heap-property) encodes both the
   leftist and the heap properties into a data type. Most of this section is on
   the property preserving merge. Type-level features: [closed type
   families](#type-families) and [propositional equality](#propositional
   equality). Additionally, it extends on theorem proving and use of existential
   types.
 - [Simulating heap operations](#simulating-heap-operations) tests the
   functional equivalence of the heap implementations in this post. We use
   QuickCheck to simulate evaluation of _arbitrary_ sequence of insertions and
   deletions. Type-level features: [visible type-applications, explicit
   foralls](#there-is-lambda-then-there-is-lambda), and [scoped type
   variables](#quickchecking-functional-equivalence).
 - [Conclusion](#conclusion) acknowledges people who made this post possible and
   reminds some take aways.

The exposition of the code is fragmented and out of order, but [a well-organised
version of the source
code](https://github.com/madgen/verified-leftist-heap/blob/master/VerifiedLeftistHeap.hs)
exists. We won't use any libraries except
[QuickCheck](http://hackage.haskell.org/package/QuickCheck-2.13.2).

# A simple heap

A heap is a (conceptually) tree-based data structure used to quickly access and
maintain access to the maximum or the minimum of a collection of values. It
satisfies the _heap property_, that is (for a maximum heap) the label of a node
is bigger than or equal to that of its children. The following typeclass
summarises its common operations.

```haskell
class Heap heap where
  {-# MINIMAL
    isEmpty, empty,
    (singleton | insert),
    (merge | insert),
    (decompose | (findMax, deleteMax))
    #-}

  type Elem heap

  -- Predicates
  isEmpty :: heap -> Bool

  -- Access
  findMax :: heap -> Maybe (Elem heap)
  findMax = fmap fst <$> decompose

  -- Creation
  empty :: heap

  singleton :: Elem heap -> heap
  singleton = (`insert` empty)

  fromList :: [ Elem heap ] -> heap
  fromList xs = -- O(n) for leftist heaps
    case go (map singleton xs) of
      [ heap ] -> heap
      [ ]      -> empty
      _        -> error "Fatal error. Did not converge to a single heap."
    where
    go [] = []
    go [ x ] = [ x ]
    go (x : y : rest) = go (merge x y : go rest)

  -- Modification
  insert :: Elem heap -> heap -> heap
  insert x = merge (singleton x)

  merge :: heap -> heap -> heap
  heap1 `merge` heap2 =
    case decompose heap1 of
      Just (heapMax, heapRest) -> heapRest `merge` (heapMax `insert` heap2)
      Nothing                  -> heap2

  decompose :: heap -> Maybe (Elem heap, heap)
  decompose heap =
    case (findMax heap, deleteMax heap) of
      (Just heapMax, Just heapRest) -> Just (heapMax, heapRest)
      (Nothing     , Nothing      ) -> Nothing
      (Just _      , Nothing      ) -> error
        "Impossible happened. There is a max but the heap is empty."
      (Nothing     , Just _       ) -> error
        "Impossible happened. Heap is non-empty but there is a max."

  deleteMax :: heap -> Maybe heap
  deleteMax = fmap snd <$> decompose
```

This is a bit mouthful because many operations are inter-definable as reflected
by the `MINIMAL`{.haskell} pragma.

The `Elem`{.haskell} _type family_ (enabled by `TypeFamilies` extension)
associated with `Heap`{.haskell} gives the type of elements for a particular
instance. This is nothing but a function from types of containers to types of
their elements. We could have equally used `MultiParamTypeClasses` and
`FunctionalDependencies` extensions to establish the same container-element
relationship. I chose a type family here because we will use type families in a
moment anyway and because I think `Elem heap`{.haskell} has less cognitive
overhead than remembering functional dependencies between type variables.

Although `insert`{.haskell}, `findMax`{.haskell} and `deleteMax`{.haskell} are
the most commonly used operations of `Heap`{.haskell}, `merge`{.haskell} is the
one that we care the most about. For all data structures we'll use as heaps
today, implementing `isEmpty`{.haskell}, `findMax`{.haskell},
`singleton`{.haskell}, and `empty`{.haskell} are trivial. Then with
`merge`{.haskell}, we can implement `insert`{.haskell}, `fromList`{.haskell},
`decompose`{.haskell}, and `deleteMax`{.haskell}. As we see in the next section,
implementing `merge`{.haskell} and deriving the rest is not only optimal in
terms of productivity but also in terms of performance for leftist
heaps.

Before implementing this interface for a leftist heap, let's look at a much
simpler instance.

```haskell
instance Ord a => Heap [ a ] where
  type Elem [ a ] = a

  isEmpty = null

  empty = []

  fromList xs = xs

  insert = (:)

  merge = (<>)

  decompose [] = Nothing
  decompose xs = Just (heapMax, left ++ tail right)
    where
    heapMax       = maximum xs
    (left, right) = span (/= heapMax) xs
```

This may be the easiest heap implementation. Insertion is $O(1)$, merging is
$O(n)$, conversion from a list is $O(1)$, and decomposing (and subsequently
finding and deleting the maximum) is $O(n)$. If it wasn't for that last $O(n)$,
this would have been a perfectly fine heap implementation, alas here we are.

This implementation is obviously correct, thus any other correct heap
implementation should be _functionally equivalent_ to it. This means performing
the same operations on two empty heaps of different implementations should
result in two heaps with the same maximum. Hence, this simple heap
implementation is perfect for [testing other implementations'
correctness](#simulating-heap-operations).

# A leftist heap

Since we'll go through the trouble of implementing leftist heaps multiple
times, let's spend a second on comparing it to array-based binary heaps.

Why bother with the leftist heap? It is persistent (hence better suited for
multi-threaded computation), purely functional, both conceptually and
implementation-wise a tree, and more resilient against off-by-one errors. Why
bother with the array-based binary heap? Better average case complexity of
insertions; its operations are in place; and it probably performs better in
practice because of good locality of reference (this is a hunch and I'd like to
be proven wrong).

We can also look at their complexities more concretely. Leftist heaps have
$O(\lg{n})$ worst-case complexity for insertion and deleting the maximum, while
maintaining $O(1)$ complexity for finding the maximum. Building a heap out of a
`Foldable`{.haskell} collection is $O(n)$. So far we're on par with binary
heaps. But we can do one better. While merging binary heaps is $O(n)$, it's only
$O(\lg{n})$ for leftist heaps. In fact, this is why insertion and deletion are
$O(\lg{n})$.

## The data structure and its properties

A leftist heap is as a tree and we implement it as such.

```haskell
data LeftistHeap a = Leaf | Node a Int (LeftistHeap a) (LeftistHeap a)
```

The tree is standard except for the `Int`{.haskell} parameter. This is the
_rank_ of the `Node`{.haskell}, which is the least distance to a
`Leaf`{.haskell}. The rank of a `Leaf`{.haskell} is 0 and the rank of a
`Node`{.haskell} is one more than the minimum of its children's ranks.

Let's briefly look at the relationship between the size of a tree and its rank.

A first question is how many elements there needs to be in the tree if its rank
is $R$? If the rank of a tree is $R$, then it must be the case that each path
from the root has $R$ `Node`{.haskell}s, otherwise the rank of the tree would be
fewer.  This means the tree has at least $2^{R} - 1$ elements.

Then the followup question is, if a tree has $N$ elements, what is its maximum
rank? Well, we know that the rank imposes a lower bound on the tree size, so
conversely, the tree size should impose a maximum on the rank. If $R$ is the
maximum rank, we have $2^{R} - 1 \leq N \lt 2^{R + 1} - 1$, so $R \leq
\lg{(N + 1)} < R + 1$. Hence, $\left\lfloor{\lg{(N
+ 1)}} \right\rfloor$ is the desired maximum.

The leftist heap has the _leftist property_. In short, the shortest path from
any node to a `Leaf`{.haskell} must be the right-most one. Since each subtree in
a leftist heap is also a leftist heap, the rank of any left child is at least as
big as that of the right, hence the name.

How can we refine the earlier calculation about the maximum rank for leftist
heaps? The distance between the root and the right-most `Leaf`{.haskell} is at
most $\left\lfloor{\lg{(N + 1)}} \right\rfloor$, if the leftist heap has $N$
elements in it. This is the critical information we'll use to derive the
complexity of the `merge`{.haskell} operation.

Accessing the rank is handy, so let's create a typeclass for it.

```haskell
class HasRank a where
  type RankType a
  rank :: a -> RankType a

instance HasRank (LeftistHeap a) where
  type RankType (LeftistHeap a) = Int

  rank Leaf           = 0
  rank (Node _ r _ _) = r
```

Here is the `Heap`{.haskell} instance for the `LeftistHeap`{.haskell}. The
`Ord`{.haskell} constraint is for the heap property. The element of a
`LeftistHeap a`{.haskell} is `a`{.haskell}. Its operations are implemented over
the next two sections.

```haskell
instance Ord a => Heap (LeftistHeap a) where
  type Elem (LeftistHeap a) = a
```

## Merging two heaps

Let's tackle the most important operation head-on.

```haskell
merge Leaf heap = heap
merge heap Leaf = heap
merge h1@(Node x _ left1 right1)
      h2@(Node y _ left2 right2) =
  if x > y
    then mkNode x left1 (merge right1 h2)
    else mkNode y left2 (merge right2 h1)
  where
  mkNode :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
  mkNode a heap1 heap2 =
    if rank heap1 <= rank heap2
      then Node a (rank heap1 + 1) heap2 heap1
      else Node a (rank heap2 + 1) heap1 heap2
```

The base cases are simple as `Leaf`{.haskell} acts as the identity element for
`merge`{.haskell}.

In the recursive case, we walk over the right-most paths of the input heaps. You
can see this in the recursive calls; they never touch the left children.

To preserve the heap property, we recurse on the right child of the argument
heap with the bigger label.

To build a new node, we use `mkNode`{.haskell} helper rather than
`Node`{.haskell} constructor directly. The helper does two things. First, it
makes the child with the lowest rank the right child. Since the arguments to
`mkNode`{.haskell} are leftist heaps themselves, this flip ensures the
right-most path to `Leaf`{.haskell} is still the shortest. Second, it calculates
the new rank which is one more than the rank of the right child.

Now what is the complexity of this? At each recursive call we potentially do a
flip, increase the rank, and construct a tree node, these are all constant time
operations. So the question is how many recursive calls there are. If the
leftist heaps being merged have $L$ and $R$ elements inside, we know their right
spines are at most length $\left\lfloor lg{(L + 1)}\right\rfloor$ and
$\left\lfloor lg{(R + 1)}\right\rfloor$ respectively. Hence, we at most do
$\left\lfloor\lg{(L + 1)} + \lg{(R + 1)}\right\rfloor$ calls. So the overall
complexity is $O(\lg{(L \times R)})$ which is a subset of $O(\lg{(L + R)})$ (can
you see why?). In short, the merge operation is logarithmic in the size of the
output.

This is not where the beauty of `merge`{.haskell} ends. Recall that most leftist
heap elements live outside the right-most path. Then since we only recurse over
the right-most path, we never touch the trees where most elements live. We just
move them around. In a purely functional language, this means the output tree
does not have to allocate new memory for those trees, it can just share them
with the input heaps.

## Every other operation

The remaining operations needed to satisfy the typeclass are as follows.

```haskell
isEmpty Leaf = True
isEmpty _    = False

empty = Leaf

singleton x = Node x 1 Leaf Leaf

decompose Leaf                  = Nothing
decompose (Node x _ left right) = Just (x, merge left right)
```

From `merge`{.haskell} follows everything else. Maximum is maintained at the
root, so accessing it is easy. The `decompose`{.haskell} operation returns the
maximum along with the rest of the heap with the maximum removed by merging the
two children of the root. Insertion (the default implementation) creates a
singleton heap out of the inserted label and merges it into the heap.

Since `merge`{.haskell} has logarithmic complexity, so does `insert`{.haskell}
and `deleteMax`{.haskell}.  Since we store the maximum at the root,
`findMax`{.haskell} runs in constant time.

Conversion from a list is more interesting. The obvious implementation is to
fold over the list of elements and insert them into the heap, this turns out not
to be the most efficient way. If we instead turn each element into a singleton
heap and repeatedly merge two heaps at a time (with multiple passes) until one
heap is left, conversion happens in linear time. The following default
implementation does exactly that.

```haskell
fromList :: [ Elem heap ] -> heap
fromList xs = -- O(n) for leftist heaps
  case go (map singleton xs) of
    [ heap ] -> heap
    [ ]      -> empty
    _        -> error "Impossible. Did not converge to a single heap."
  where
  go [] = []
  go [ x ] = [ x ]
  go (x : y : rest) = go (merge x y : go rest)
```

Why does this run in linear time? Assume for simplicity that there are $2^R$
elements. Then in the first pass, we do $2^{R-1}$ $O(\lg{2})$ operations. In the
next pass, we do $2^{R-2}$ $O(\lg{4})$, then $2^{R-3}$ $O(\lg{8})$ operations
and so on. So the overall complexity is $O(\sum^{R}_{i = 1}{(\lg{2^i})
2^{R-i}}\,)$ which is $O(\sum^{R}_{i = 1}{i \; 2^{R-i}}\,)$ and that is
$O(2^{R})$. That is the number of elements we started with, so conversion from a
list is done in linear time.

# Terms, types, and kinds

Before doing verification with fancy types, we need to understand terms, types,
and kinds. Here's the gist: all terms have types, all types have kinds, and
there is no distinction between types and kinds since GHC 8.0, but terms and
types (for now) occupy different realms.

For example, just as you can say `42 :: Int`{.haskell}, you can also say `Int ::
Type`{.haskell} and `Type :: Type`{.haskell} (`*`{.haskell} is a deprecated
synonym of `Type`{.haskell}; import `Data.Kind`{.haskell} for `Type`{.haskell}).
We can read these as "`42`{.haskell} is an `Int`{.haskell}", "`Int`{.haskell} is
a `Type`{.haskell}", and "`Type`{.haskell} is a `Type`{.haskell}" (yup, not a
typo).

Just as you can use `:type` or `:t` learn the type of a term in `ghci`, you can
use `:k` or `:kind` to learn the kind of a type.

We now look at types and kinds in more detail. It may be too much information to
soak in at once, but the broad-strokes should be enough for this post. For more
detailed and broad overview of the subject, see Diogo Castro's amazing [blog
post](https://diogocastro.com/blog/2018/10/17/haskells-kind-system-a-primer/).
More generally, one can get away without an in-depth understanding of these and
still be able to verify data structures. But then we'd be relying on GHC to yell
at us when certain extensions are missing and not understand why we're being
yelled at.

## Proofs and contradictions

Famously, Ludwig Wittgenstein wasn't terribly concerned about inconsistencies in
mathematics as most were, including Alan Turing. They even have a [direct
exchange](https://www.britishwittgensteinsociety.org/wp-content/uploads/documents/lectures/Turing-and-Wittgenstein-on-Logic-and-Mathematics.pdf)
on this subject. Surprisingly, Haskell's type system seems to agree more with
Wittgenstein than with Turing.

If `Type :: Type`{.haskell} makes you uncomfortable, you're right, it is
problematic and it leads to [Russel's
paradox](https://en.wikipedia.org/wiki/Russell%27s_paradox). This is one reason
people don't like type-level programming in Haskell. It means as a proof system,
Haskell's type system is inconsistent. What that means is that _we don't have
the ability to tell the truth_. The expectation due to the [Curry-Howard
correspondance](https://en.wikipedia.org/wiki/Curry–Howard_correspondence) is
that if we have a type corresponding to some logical statement, a term for that
type (if it exists) is a proof. Inconsistency means, we can have terms that are
not valid proofs of the statement, but satisfy the type checker.  In particular,
`Type :: Type`{.haskell} leads to diverging terms that can satisfy any
proposition.

That said, since Haskell already has `let x = x in x`{.haskell},
`undefined`{.haskell}, and `error "QED"`{.haskell} satisfying types of
propositions, we didn't have the ability to tell the truth to start with. Hence,
we are not worse off. At least, this is the argument in Prof. Stephanie
Weirich's [paper](http://www.seas.upenn.edu/~sweirich/papers/fckinds.pdf) as
well as [the GHC
documentation](https://downloads.haskell.org/~ghc/8.8.1/docs/html/users_guide/glasgow_exts.html#overview-of-type-in-type).

One might think existing flaws don't justify adding new ways to break a system.
Ordinarily, that's right, but contradictions are infectious. As soon as there is
a little crack, it is difficult to contain. So the marginal harm done by `Type
:: Type`{.haskell} is less than expected.

There are such things as [_paraconsistent
logics_](https://en.wikipedia.org/wiki/Paraconsistent_logic) that try to limit
the harm done by contradiction, but they are not employed in type systems as far
as I know.

To sum up, Haskell proofs are partial. If a term (proof) corresponding to a type
(proposition) compiles, one of two things happened. The term is a valid proof or
its evaluation will diverge. In contrast, Agda and Idris proofs are always
terminating and are thus valid proofs as long as the type checker says so (up to
compiler bugs). Hence, despite the syntactic similarity, you should have more
faith in the latter.

## Why is `Type`{.haskell} a misnomer?

The kind `Type`{.haskell} has a very confusing name. It should really be named
`LiftedType`{.haskell}. Let's understand why.

It has two important features. The term `undefined`{.haskell} (or $\bot$ in
academic papers) is a valid term for any type with kind `Type`{.haskell}. This
makes `Type` the kind of _lifted_ types. Consequently, all of these types are
_inhabited_.

GHC manual (until recently) called `Type`{.haskell} "the kind of types with
values". This is not true. If we enable `MagicHash` extension, we get access to
unlifted types such as `Int#`{.haskell}. `Int#`{.haskell} definitely has values
as witnessed by `42# :: Int#`{.haskell}, but when we query `:k Int# ::
Type`{.haskell}, we get an error saying "Expecting a lifted type, but
`Int#`{.haskell} is unlifted". So there are inhabited types without kind
`Type`{.haskell}.

It is also wrong to say that `Type`{.haskell} is the kind of types that
definitely has inhabitants. Once again the kind of `Int#`{.haskell} is `TYPE
'IntRep`{.haskell} and `Int#`{.haskell} is the only type of that kind. We
already know it has inhabitants. In fact, in a sense `TYPE 'IntRep`{.haskell} is
superior because `data Void`{.haskell} creates a type `Void :: Type`{.haskell}
where the only inhabitants are degenerate such as `error "Oops!"`{.haskell} and
`undefined`{.haskell}. Neither of these are proper values. `TYPE
'IntRep`{.haskell} can claim to be _a_ kind of types that has non-degenerate
inhabitants.

As a final piece of evidence about why `Type`{.haskell} is a bad name, you can
consult `GHC.Types`{.haskell} which defines the kind `Type`{.haskell} as `TYPE
'LiftedRep`{.haskell}. Even GHC admits that `Type`{.haskell} is more specific
than what the name implies.

So `Type`{.haskell} is a bad name because of non-`Type`{.haskell} types! We've
already seen `Int#`{.haskell},
let's find some more.

## `Type`{.haskell} constructors

`Maybe`{.haskell} takes a `Type`{.haskell} and returns a `Type`{.haskell}. How
about `Either`{.haskell}? It takes two `Type`{.haskell}s and returns a
`Type`{.haskell}. You can say they are type-level functions and you wouldn't be
wrong, but we can be more specific. We can say that `Maybe`{.haskell} and
`Either`{.haskell} construct `Type`{.haskell}s just like `(:)`{.haskell} and
`[]`{.haskell} at the term level.

Are `Maybe`{.haskell} and `Either`{.haskell} types themselves? They are types
but not `Type`{.haskell}s.  Asking `ghci` reveals that `Maybe`{.haskell} has
kind `Type -> Type`{.haskell} and `Either`{.haskell} has kind `Type -> Type ->
Type`{.haskell}.

`Type -> Type`{.haskell} is not the same thing as `Type`{.haskell}, but (here is
the confusing part) `Type -> Type`{.haskell} has the kind `Type`{.haskell}. Get
your head around that! If you can't, that's fine. The intuition is that types
and kinds are one and the same, then so are the function arrow `(->)`{.haskell}
and kind arrow `(->)`{.haskell}. A more concrete explanation will follow once we
cover [levity polymorphism](#levity-polymorphism). One implication of `Type ->
Type :: Type` is that, it is inhabited. For example, `id :: Type -> Type` type
checks.

We have `Type`{.haskell}s; we have things that construct `Type`{.haskell}s; and
we have unlifted types such as `Int#`{.haskell}. What else?

## Data type promotion

So far, we've only seen inhabited types. `Int`{.haskell} and `Int#`{.haskell}
are obviously examples, but `Type -> Type`{.haskell} is also inhabited since
that too has kind `Type`{.haskell}.

Emphasising inhabitation as a property implies that there must be some
uninhabited kinds. In fact, these are the pillars of theorem proving and
property encoding in Haskell.

Consider the following `List`{.haskell} declaration.

```haskell
data List a = Nil | Cons a (List a)
```

In vanilla Haskell, this generates a type `List`{.haskell} and two data
constructors `Nil`{.haskell} and `Cons`{.haskell}.

```haskell
List :: Type -> Type
Nil  :: List a
Cons :: a -> List a -> List a
```

With `DataKinds` extension, you also get following.

```haskell
'Nil  :: List a
'Cons :: a -> List a -> List a
```

Despite looking pretty similar, these are different beasts. Since there is no
distinction between types and kinds, the type constructor `List`{.haskell} is
also a kind constructor. Then, `'Nil`{.haskell} and `'Cons`{.haskell} are type
constructors, but they are not `Type`{.haskell} constructors, they are `List
a`{.haskell} constructors! All promoted types are automatically uninhabited. So
there is no term `t`{.haskell} with `t :: 'Cons Int 'Nil`{.haskell}.

This promotion feature alone spawns multiple reasons why people do not like
fancy types in Haskell:

  1. The `'` prefix of promoted type-constructors is optional, but terms and
  types are completely separate. So when I type `Nil`{.haskell}, GHC figures out
  whether it is a term or a type constructor depending on the context. In the
  absence of `'`, we need to disambiguate ourselves.

  2. The built-in list type `[a]`{.haskell} is automatically promoted. This
  means there is `[]`{.haskell}, the equivalent of `Nil`{.haskell}. There is
  `[]`{.haskell}, the type and kind constructor equivalent to `List`{.haskell}.
  Then there is `'[]`{.haskell}, the type constructor equivalent to
  `'Nil`{.haskell}. Remember that `'` is optional. So when I use `[]`{.haskell},
  we don't know, if it is the type constructor `List`{.haskell} or the type
  constructor `Nil`{.haskell}. Similar situation occurs with tuples, where the
  term and the type share similar syntax.

Note that this is the improved state of affairs. Kinds and types used to be
separated and there was also a separate kind `[]`{.haskell} with sort (the
classification of kind) `BOX`{.haskell}.

Nevertheless, promoted types are a blessing. They act as indices to other data
types and allows us to encode various properties at type level. We come back to
this when we introduces GADTs.

## Kind polymorphism

Just as there are polymorphic types such as `[a] -> [a]`{.haskell}, there are
also polymorphic kinds. In fact, `'Cons`{.haskell} has kind `a -> List a -> List
a`{.haskell} where `a`{.haskell} is a kind variable. We can see this in `ghci`.

The kind variable `a`{.haskell} can be `Type`{.haskell},

```haskell
> :k 'Cons Int
'Cons Int :: List Type -> List Type
```

Or it can be the kind of a type constructor such as `Type -> Type`{.haskell}

```haskell
> :k 'Cons Maybe
'Cons Maybe :: List (Type -> Type) -> List (Type -> Type)'
```

We can also use a promoted kind such as `List a`{.haskell}, which results in
another kind polymorphic type.

```haskell
> :k 'Cons 'Nil
'Cons 'Nil :: List (List a) -> List (List a)
```

## Levity polymorphism

The distinction between types that have inhabitants and types that don't stand
on solid ground in GHC and leads to beautiful generalisations over types that
have inhabitants. We now explore that.

This section consolidates the previous discussions of type habitation. If your
solely interested in verification, you can skip it.

What is the kind of the `Type`{.haskell} constructor `List`{.haskell}?

```haskell
> :k List
Type -> Type
```

The return kind makes sense, it's a `Type`{.haskell} constructor after all, but
why the input kind `Type`{.haskell}? Since `Cons`{.haskell}'s first parameter
has type `a`{.haskell}, constructing a term `Cons x xs`{.haskell} necessitates a
term `x :: a`{.haskell}, hence `a`{.haskell} must be a type with kind
`Type`{.haskell}.

Hopefully, my rant about `Type`{.haskell} being a misnomer made you doubt the
last statement. What about `Int#`{.haskell}? Since `Int#`{.haskell} has
inhabitants, by the reasoning above `a`{.haskell} can also be `Int#`{.haskell}.
More generally, we want `a`{.haskell} to be a type that has a runtime
representation.

You remember `TYPE`{.haskell}? The kind that spawns `Type`{.haskell} and `TYPE
'IntRep`{.haskell}. Let see what kind it has.

```haskell
> :k TYPE
TYPE :: RuntimeRep -> Type
```

Aha! `TYPE`{.haskell} constructs things that have runtime representations. So we
want the type variable of `List`{.haskell} to have kind `TYPE rep`{.haskell}, so
that it ranges over everything that has a runtime representation. This idea of
abstracting over runtime representations is called _levity polymorphism_.

But why doesn't GHC infer that as the kind of `a`{.haskell}? Let's try declaring
a levity polymorphic `List` explicitly.

```haskell
> data List (a :: TYPE rep) = Nil | Cons a (List a)
```
```
A levity-polymorphic type is not allowed here:
  Type: a
  Kind: TYPE rep
```

The reason this doesn't work and why GHC defaults `a`{.haskell} to
`Type`{.haskell} is because if we want to create a data type, we need to know
its runtime representation in advance to lay down the data while generating
code. For example, `Int#`{.haskell} requires 32 bits but `Int`{.haskell}
requires a pointer to a thunk, hence 64 bits. Unless you know how big the data
is you can't generate the code (at least not without introducing runtime code
generation or indirection which defeats the purpose of unlifted types).

More generally, [the paper introducing levity
polymorphism](https://cs.brynmawr.edu/~rae/papers/2017/levity/levity.pdf) has
the following maxim for its usage:

> Never move or store a levity-polymorphic value.

This rules out making a function as simple as `id`{.haskell} levity polymorphic
as well because it moves values.

This raises the question, what can be levity polymorphic then? The classic
example is `error`{.haskell}. It has type `String -> a`{.haskell}, so `a` needs
to be runtime representable. It neither stores nor moves a value and
`a`{.haskell}. Hence, it can be and is levity polymorphic in GHC:

```haskell
error :: forall (rep :: RuntimeRep) (a :: TYPE rep). String -> a
```

You need `-fprint-explicit-runtime-reps` flag and the `+v` option to `:t` to get
the signature.

```
> :set -fprint-explicit-runtime-reps
> :t +v error
```

Let's look at something more interesting. What is the kind of the function type
constructor `(->)`{.haskell}?

```haskell
(->) :: forall {r :: RuntimeRep} {s :: RuntimeRep}.  TYPE r -> TYPE s -> Type
```

This shows why `Type -> Type`{.haskell} has inhabitants. It is because
`(->)`{.haskell} is a `Type`{.haskell} constructor. More importantly, it shows
that when you write a function between lifted data types or from a lifted data
type to a unlifted one, we are in fact using the same arrow rather than
syntactic magic.

## Inhabitable out of uninhabitable

What is the kind of the following data type?

```haskell
data MyProxy a = MkMyProxy
```

If we ask `ghci`, we get `Type -> Type`{.haskell} again. However, this time
`a`{.haskell} does not appear as a type parameter to the sole constructor of
`MyProxy`{.haskell}, so there is no reason for it to have a runtime
representation. In principle, the type argument to `MyProxy`{.haskell} can be
_anything_. This sounds kind polymorphic.

GHC, by default, assumes that the type variables of a type constructor have the
kind `Type`{.haskell} even if they can be more generic. If you turn on the
`PolyKinds` extension, GHC correctly infers the kind `k -> Type`{.haskell} to
`Proxy`{.haskell}, where `k`{.haskell} is a kind variable.

This is nice because it is general, but also unmotivated at the moment because
we haven't yet made any use of poly-kindedness.
[Later](#propositional-equality), we define a poly-kinded equality type
illustrating the utility of kind polymorphism.

## Summary

Haskell is slowly evolving into a practical language that unifies terms and
types. We are not quite there yet and the gradual transition creates some
interesting and tough-to-wrap-your-head-around language concepts. This section
gives a bird eye's view of these concepts that we shall use as building blocks
of useful type-level programming.

# Verifying the leftist property

Let's encode the leftist property in a data type. That is, we will ensure that
each the rank of each right child of a node is less than or equal to the rank of
its left child. This necessitates access to ranks at the type-level. Previously,
we used `Int`{.haskell} for ranks, but ranks are really just natural numbers.

We have two (main) options for type-level natural:

 1. importing `GHC.TypeLits`{.haskell}, which uses compiler magic to define a
 `Nat`{.haskell} kind
 2. or defining a `Nat`{.haskell} kind inductively from scratch.

The advantage of (1) is it is efficient and we get to use numeric literals such
as `42`{.haskell}. The advantage of (2) is that it is not compiler magic and we
get to see how theorem proving works in action. Hence, we'll do (2).

If you reproduce this implementation using (1), you should probably use [the
`singletons` library](http://hackage.haskell.org/package/singletons) to fake
dependent types and the fantastic GHC type-checker plugin
[`ghc-typelits-natnormalise`](http://hackage.haskell.org/package/ghc-typelits-natnormalise-0.7)
to use arithmetic properties of natural numbers. Because type-level naturals are
not inductively defined, we can't do the kind of proofs that dependently-typed
languages are good at. Thus, we rely on external solvers.

Here's the plan: reinvent natural numbers and $\leq$; use those to define a data
type that makes non-leftist heaps illegal; attempt and fail to define
`merge`{.haskell}; go prove some properties about natural numbers; and finally
succeed at implementing `merge`{.haskell}. Ready? It will be fun; I promise.

## Natural numbers

We need the type-level natural numbers and $\leq$ relation between them.
Let's start with naturals.

```haskell
data Nat = Z | S Nat deriving (Eq, Show)
```

This gives us a type and a kind `Nat`{.haskell}, data constructors `Z ::
Nat`{.haskell} and `S :: Nat -> Nat`{.haskell}, and type constructors `'Z :: Nat
-> Nat`{.haskell} and `'S :: Nat -> Nat`{.haskell}.

### Generalised algebraic data types

Type-level naturals were pretty easy. Next, we need to define the $\leq$
relation using generalised algebraic data types (GADTs) enabled via `GADTs`
extension. However, since $\leq$ is a mean first example for GADTs, we start
with natural numbers that remember whether they are zero or not at the type
level.

GADTs provide an alternative syntax for declaring data types and the ability to
discriminate types based on constructors. The `AnotherNat`{.haskell} data type
in GADT syntax below is exactly the same as `Nat`{.haskell}.

```haskell
data AnotherNat :: Type where
  AZ ::               AnotherNat
  AS :: AnotherNat -> AnotherNat
```

The (boring) return types of constructors are now explicit. GADTs shine when the
constructor choice affects the return type. Consider a data type for natural
numbers encoding zeroness of a natural.

```haskell
data Zeroness = Zero | NonZero

data TaggedNat :: Zeroness -> Type where
  TZ ::                TaggedNat 'Zero
  TS :: TaggedNat a -> TaggedNat 'NonZero
```

This says if a term is constructed using `TZ`{.haskell}, we have a
`'Zero`{.haskell} natural. But if it is constructed with `TS`{.haskell} instead,
regardless the natural number being succeeded, we have a `'NonZero`{.haskell}
natural number.

With this we can write a total function a `div :: TaggedNat a -> TaggedNat
'NonZero -> TaggedNat b`{.haskell} and the compiler will complain every time we
try to divide by zero.

Now if we implement `div`{.haskell}, it is tempting to be a good developer and
write the following case.

```haskell
div _ TZ = error "Impossible! The compiler ensures it!"
```

Doing so prompts GHC to kindly inform us that this case cannot occur and thus is
not needed. In fact, GHC wouldn't even bother generating the code to raise the
infamous "non-exhaustive patterns" exception because it knows the type checker
wouldn't let such an offence reach code generation. So not only GADTs improve
safety, but also, other things equal, generate less code and consequently
improve efficiency.

### Less than or equal to relation

Let's finally define $\leq$.`TypeOperators` extension is needed to use infix
operators at the type level.

```haskell
data (<=) :: Nat -> Nat -> Type where
  Base   ::             'Z <= 'Z
  Single :: n <= m ->    n <= 'S m
  Double :: n <= m -> 'S n <= 'S m
```

This defines a relation between two `Nat`{.haskell}s. It records a series of
steps that gets us to the desired $n \leq m$ starting from an indisputable fact.
The record of these steps constitute a term which witnesses that the relation
holds.

The indisputable fact is $\vdash_{\mathit{PA}} 0 \leq 0$ encoded by the
`Base`{.haskell} constructor. Then by applying a series of `Single`{.haskell}s
and `Double`{.haskell}s, we try to produce the desired inequality $n \leq m$.
These constructors encode the following statements: $\vdash_{\mathit{PA}} n \leq
m \implies n \leq m + 1$, and $\vdash_{\mathit{PA}} n \leq m \implies n + 1 \leq
m + 1$. Hopefully, neither are controversial as our verification claims hinge on
these being sound.

For example, to establish $1 \leq 2$ we need to give a term of type `'S 'Z <= 'S
('S 'Z)`{.haskell}.

```haskell
oneLEQtwo :: 'S 'Z <= 'S ('S 'Z)
oneLEQtwo = Single $ Double $ Base
```

This proof can be read as "from $0 \leq 0$, we can get to $1 \leq 1$ by
incrementing both sides; and from there, we can get to $1 \leq 2$ by incrementing
the right side.".

Besides soundness, we also care about _completeness_. Is it the case that by
applying `Single`{.haskell}s and `Double`{.haskell}s to `Base`, we can get to
all valid $n \leq m$? Yes, but we won't prove it in this post. In fact there are
multitude of ways of proving a valid $n \leq m$. As an example, let's look
at another proof of `oneLEQtwo`{.haskell}.

```haskell
oneLEQtwo' :: 'S 'Z <= 'S ('S 'Z)
oneLEQtwo' = Double $ Single $ Base
```

You might have noticed that, the order of `Single`{.haskell}s and
`Double`{.haskell}s doesn't matter. Then, a proof of $n \leq m$ always starts
with `Base`{.haskell}, and is followed by $m - n$ `Single`{.haskell}s and $n$
`Double`{.haskell}s in any order.

### Singletons: faking dependent types

We can use the insight for reaching a valid $n \leq m$ to recover $n$ and $m$
given an inequality. What would be the type of a function doing that?  We could
try the following.

```haskell
recoverAttempt :: n <= m -> (n,m)
recoverAttempt = undefined
```

This doesn't work because $n$ and $m$ have kind `Nat`{.haskell} but the
`(,)`{.haskell} type constructor has the kind signature `Type -> Type ->
Type`{.haskell}. So is it just the case that `(,)`{.haskell} is not the right
kind of container? The problem runs deeper. Eventually we want access to
`n`{.haskell} and `m`{.haskell} at runtime, this implies there should be some
terms `t :: n`{.haskell} and `r :: m`{.haskell}. We know this won't work because
`n`{.haskell} and `m`{.haskell} have kind `Nat`{.haskell} and types of that kind
don't have inhabitants.

In a dependently-typed language this wouldn't be an issue because there is no
distinction between terms and types, so every entity, let it be term or type,
can survive compilation.

Sadly, Haskell is not there yet, so we need to fake it using _singletons_. The
idea is to create an indexed data type, so that there is exactly one term for
each indexing type. That is all a bit vague, let's just do it for naturals.

```haskell
data SNat :: Nat -> Type where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)
```

You see while the type `'Z`{.haskell} has kind `Nat`{.haskell}, the type `SNat
'Z`{.haskell} has kind `Type`{.haskell} and it has exactly one inhabitant:
`SZ`{.haskell}. This correspondence is true for all naturals. Hence, we can use
the singleton type `SNat n :: Type`{.haskell} as the term-level representative
for `n :: Nat`{.haskell}.

Now, we can write the recovery function.

```haskell
recover :: n <= m -> (SNat n, SNat m)
recover Base = (SZ, SZ)
recover (Single nLEQsm) | (x,y) <- recover nLEQsm = (   x, SS y)
recover (Double nLEQm)  | (x,y) <- recover nLEQm  = (SS x, SS y)
```

This function uses the inductive structure of `n <= m`{.haskell}. We know from
their types that, `Single`{.haskell} increments the right side of `<=`{.haskell}
and `Double`{.haskell} increments both sides. We just turn them to explicit
increments to recover the singletons for `n`{.haskell} and `m`{.haskell}.

In fact, we can be sure that our implementation is correct. The type is so
specific that unless we use a degenerate term like `undefined`{.haskell}, there
was no way of getting a buggy implementation to type check.

## Rank encoded leftist heaps

We have everything needed to encode the leftist property at type level. Since
the leftist property involves comparing ranks of subheaps, we need access to
rank at type level. `Rank`{.haskell} does that using a an `SNat`{.haskell}. We
also define a helper to increment the rank for later use.

```haskell
newtype Rank n = Rank { _unRank :: SNat n }

inc :: Rank rank -> Rank ('S rank)
inc (Rank snat) = Rank (SS snat)
```

Since heaps need to be indexed by their rank, we use a GADT.

```haskell
data SafeHeap :: Nat -> Type -> Type where
  Leaf' :: SafeHeap 'Z a
  Node' :: a -> Rank ('S m)             -- Node' data
        -> SafeHeap n a -> SafeHeap m a -- Children
        -> m <= n                       -- Leftist invariant
        -> SafeHeap ('S m) a
```

This data type hopefully doesn't look scary anymore. The `Leaf'`{.haskell}
constructor creates a `SafeHeap`{.haskell} of rank 0. The `Node'`{.haskell}
constructor grows the heap only when we can show that the rank of the right
subheap is less than or equal to that of the left subheap. Further, the
resulting heap has rank one more than that of the right subheap.

What did we just do? We created a data type whose inhabitants are either vacuous
or that it is a tree satisfying the leftist property. Let's try some examples.

```haskell
heap1 :: SafeHeap ('S 'Z) Int
heap1 = Leaf'
```

This fails because the `Leaf'`{.haskell} forces the rank to be `'Z`{.haskell}
instead of `'S 'Z`{.haskell} as required by the signature.

```haskell
heap2 :: SafeHeap ('S 'Z) Int
heap2 = Node' 42 ('SS 'SZ) Leaf' Leaf' Base
```

This type checks because `Leaf'`{.haskell}s has rank `'Z`{.haskell} and
`Base`{.haskell} proves `'Z <= 'Z`{.haskell}.

```haskell
heap3 :: SafeHeap ('S 'Z) Int
heap3 = Node' 42 ('SS 'SZ) heap2' Leaf' (Single Base)
```

This also type checks because the right child has a lower rank (`'Z`{.haskell})
than the left child (`'S 'Z`{.haskell}) and `Single Base`{.haskell} proves `'Z
<= 'S 'Z`{.haskell}.

```haskell
heap4 :: SafeHeap ('S 'Z) Int
heap4 = Node' 42 ('SS 'SZ) Leaf' heap2' ???
```

Unless we replace `???`{.haskell} with a degenerate term, we won't be able to
find a proof for `'S 'Z <= 'Z`{.haskell} on the account of its being false. This
is precisely how the data type prevents us from violating the leftist property.

We just made terms that violate the leftist property illegal. Pretty cool, huh?

## Heap instance for SafeHeap

Making property violating terms illegal is one thing, defining operations on
them another.

The `Heap`{.haskell} instance for `LeftistHeap`{.haskell} was directly on that
data type. Consequently, the signatures of heap operations all involved
`LeftistHeap`{.haskell}. This direct approach tends fail with property encoding
fancy types.

Say we tried to make `SafeHeap rank a`{.haskell} an instance of
`Heap`{.haskell}.

```haskell
instance Ord a => Heap (SafeHeap rank a) where
  type Elem (SafeHeap rank a) = a
```

We're already in a bad place. This forces the type of `merge`{.haskell} to be
`SafeHeap rank a -> SafeHeap rank a -> SafeHeap rank a`{.haskell}. This type is
too restrictive! We want to be able to merge heaps of different ranks and to
produce a heap of rank not identical to the input heaps.

Let's say that we gave up on the typeclass and decided to define all the
operations at the top-level. Then we could give `merge`{.haskell} the type
`SafeHeap rank1 a -> SafeHeap rank2 a -> SafeHeap (Fx rank1 rank2) a`{.haskell}.
Here `Fx`{.haskell} is some type-level function. This allows inputting heaps of
different ranks. We still need to figure out the rank of the output, but that
_depends_ on the input heaps in their entirety not just their ranks. The word
"depend" is a red flag. Do we need to create singletons for
`SafeHeap`{.haskell}s as well?  Clearly, this line of thinking leads to too much
work.

What was our original goal? It was to preserve the leftist property. Does that
require knowing the effects of operations on the rank of the heap at type level?
No, not really. For `merge`, we want to input two `SafeHeap`{.haskell}s of
_some_ rank and produce a `SafeHeap`{.haskell} of _some_ rank. The fact that the
output is a `SafeHeap`{.haskell} is enough to ensure the leftist property is
preserved, which is our goal.

So we want to perform the operations a data type that is indifferent to the rank
at the type-level just as the untyped version was. Existential types enabled via
`ExistentialQuantification` can achieve this.

```haskell
data SomeSafeHeap label = forall rank. SSH (SafeHeap rank label)
```

Despite writing `forall`{.haskell}, what we mean is "within `SomeSafeHeap a`,
**there exists** a `rank`{.haskell} such that `SafeHeap rank a`{.haskell}".
Hence, the name existential types. Let's try the `Heap`{.haskell} instance
again.

```haskell
instance Ord label => Heap (SomeSafeHeap label) where
  type Elem (SomeSafeHeap label) = label
```

Now, `merge`{.haskell} has type `SomeSafeHeap a -> SomeSafeHeap a ->
SomeSafeHeap a`{.haskell} which makes no assertions about ranks. Yet its inputs
and output contain `SafeHeap`{.haskell}s and thus satisfy the leftist property.

**The key take away:** if you use fancy types, reach for the existential as soon
as possible.

This is not to say that you should never implement operations relating fancy
types of inputs and outputs. If you succeed, it will give you more static
guarantees! The question is whether they justify the effort.

The `singleton`{.haskell} function for `SomeSafeHeap a`{.haskell} is a trivial
example of this. We know that the singleton heap should have rank 1. Since rank
information is hidden behind an existential, there is nothing preventing us from
defining `singleton x` to be `empty`.

```haskell
singleton x = empty
```

This type checks just fine. One way to improve the situation is to extract the
`SafeHeap ('S 'Z) a`{.haskell} into its own definition and reduce the likelihood
of such a mistake.

```haskell
singleton x = SSH singleton'
  where
  singleton' :: SafeHeap ('S 'Z) a
  singleton' = Node' x (Rank (SS SZ)) Leaf' Leaf' Base
```

## Merging safe heaps

Here's the partial code for the `merge` operation on safe heaps.

```haskell
merge (SSH Leaf') heap = heap
merge heap (SSH Leaf') = heap
merge heap1@(SSH (Node' x _ left1 right1 _))
      heap2@(SSH (Node' y _ left2 right2 _)) =
  if x > y
    then mkNode x (SSH left1) (merge (SSH right1) heap2)
    else mkNode y (SSH left2) (merge (SSH right2) heap1)
  where
  mkNode :: a -> SomeSafeHeap a -> SomeSafeHeap a -> SomeSafeHeap a
  mkNode a (SSH h1) (SSH h2) = _
```

This bit is almost identical to the unverified version except for some
unwrapping and wrapping with `SSH`{.haskell}. This makes sense because as we
pointed in the unverified version, `mkNode`{.haskell} is where the leftist
property is preserved by placing the heap with the smaller rank to the right.

### Comparing without forgetting

In unverified leftist heap's `mkNode`{.haskell}, the term-level `(<=)`{.haskell}
operator decided on which child is placed to the right. It seems all we need is
to provide an analogous operator for `SNat`{.haskell}s. However, we now also
need a proof that the rank of the right child is less than the rank of the left
child. Sadly, `(<=)`{.haskell} determines the desired property and forgets it
immediately by returning a `Bool`.

What we want here is _connexity_, that is given any $n$ and $m$, either $n \leq
m$ or $m \leq n$. This holds for [total
orders](https://en.wikipedia.org/wiki/Total_order) including $\leq$ on natural
numbers. We can express this in Haskell easily.

```haskell
lemConnexity :: SNat n -> SNat m -> Either (n <= m) (m <= n)
lemConnexity SZ y = Left  (lemZLEQAll y)
lemConnexity x SZ = Right (lemZLEQAll x)
```

The base cases are simple, we need to show $0 \leq m$ and $0 \leq n$. A lemma
for $0 \leq x$ holds for all $x$ would handle both cases. Let's suppose
`lemZLEQAll :: SNat n -> Z' <= n`{.haskell} for the moment. This make-believe with
lemmas is how top-down proofs work. To focus on the proof at hand, we
postulate reasonable looking statements.

The inductive case is also simple and is a good opportunity to demonstrate doing
proofs with _typed holes_.

```haskell
lemConnexity (SS x) (SS y) = _
```

Since `SNat`{.haskell} is a GADT, pattern matching on `SS`{.haskell} refines the
type we need to provide for `_`{.haskell}. At this point, it is `Either ('S n1
<= 'S n2) ('S n2 <= 'S n1)`{.haskell}. If we had `Either (n1 <= n2) (n2 <=
n1)`{.haskell}, we could proceed from there. A recursively call to
`lemConnexity` gives us that.

```haskell
lemConnexity (SS x) (SS y) =
 case lemConnexity x y of
   Left  xLEQy -> _
   Right yLEQx -> _
```

Now we have two typed holes. We are trying to get to `Either ('S n1 <= 'S n2)
('S n2 <= 'S n1)`{.haskell} from `xLEQy :: n1 <= n2`{.haskell} and `yLEQX :: n2
<= n1`{.haskell} respectively. The `Double` constructor produces a new
inequality from an existing one by incrementing both sides. Combined with
`Left`{.haskell} or `Right`{.haskell} depending on the case, we reach a term of
the desired type.

```haskell
lemConnexity (SS x) (SS y) =
 case lemConnexity x y of
   Left  xLEQy -> Left  (Double xLEQy)
   Right yLEQx -> Right (Double yLEQx)
```

We are now almost done with `lemConnexity`{.haskell}. Earlier we postulated
`lemZLEQAll`{.haskell}, so we still need to prove that. It is another induction
over naturals.

```haskell
lemZLEQAll :: SNat n -> 'Z <= n
lemZLEQAll SZ     = Base
lemZLEQAll (SS x) = Single (lemZLEQAll x)
```

That's it. We just proved some order theoretic properties.

The ergonomics of this process is lacking. Errors are not a productive way to
interact with typed holes. Inspecting terms and their types available at a given
hole without clutter would be useful, but GHC spits 50 lines per hole and very
little of that is helpful. There isn't much help with crafting the proof either.

By contrast, Idris and Agda provide editor integration to quickly inspect the
context of holes, to search and fill in terms that satisfy the hole, and to
refine the whole when given a partial expression.

That said, with some discipline about making the lemmas small and properties
simple, we can go a long distance as long as we are not trying to mechanise an
entire field of mathematics.

### Making nodes with proofs

By harnessing `lemConnexity`, implementing `mkNode` is a breeze.

```haskell
mkNode :: a -> SomeSafeHeap a -> SomeSafeHeap a -> SomeSafeHeap a
mkNode a (SSH h1) (SSH h2) =
  case lemConnexity (_unRank . rank $ h1) (_unRank . rank $ h2) of
    Left  r1LEQr2 -> SSH $ Node' a (inc $ rank h1) h2 h1 r1LEQr2
    Right r2LEQr1 -> SSH $ Node' a (inc $ rank h2) h1 h2 r2LEQr1
```

The lemma tells us which heap has the lower rank (hence needs to be the right
child) as well as giving us a proof for it which is all that is needed to
construct a `Node'`{.haskell}.

# Verifying the heap property

Let's do it one last time with both the heap and the leftist properties.

So what is the heap property mathematically? For a node $n$ and its children $l$
and $r$, it is the case that $\mathit{label}(l) \leq \mathit{label}(n)$ and
$\mathit{label}(r) \leq \mathit{label}(n)$.

We need labels in types as well as ranks. So far we used arbitrary
`Type`{.haskell}s for labels. As a simplification, we decree that they must
effectively be `SNat`{.haskell}s, so that we can build on our existing theory of
naturals.

## Rank and label encoded leftist heaps

To avoid confusion with ranks, we wrap `SNat`{.haskell}s used as labels.

```haskell
newtype Label n = Label { _unLabel :: SNat n }
```

We don't need anything else to declare the data type that makes non-heaps
illegal.

```haskell
data SaferHeap :: Nat -> Nat -> Type where
  Leaf'' :: SaferHeap 'Z 'Z
  Node'' :: Label a -> Rank ('S m)         -- Node' data
         -> SaferHeap n b -> SaferHeap m c -- Children
         -> m <= n                         -- Leftist property
         -> b <= a -> c <= a               -- Heap property
         -> SaferHeap ('S m) a
```

`SaferHeap`{.haskell} looks a lot like `SafeHeap`{.haskell}, except for
`Node''`{.haskell}'s fancy-typed label and two inequalities to maintain the heap
property.

`Leaf''`{.haskell} carries a label `'Z`{.haskell} because every
`SaferHeap`{.haskell} needs a type-level label. Using `'Z`{.haskell} is a hack.
It is the least natural number, hence it can't inhibit a `Node''`{.haskell}
construction whatever its label may be.

There are two immediate alternatives to this:

 1. Using `Maybe (SNat n)`{.haskell} rather than `SNat n`{.haskell} for the
 label. This requires modifying the heap property so that rather than `b <= a`,
 we'd need "given `b`{.haskell} is `'Just b'`{.haskell}, `b' <= a`{.haskell}"
 and similarly for `c <= a`{.haskell}.

 2. Using `Maybe (SNat n)`{.haskell} again, but instead of changing the heap
 property, we create three `Node''`{.haskell} like constructors: one with both
 children having `'Just`{.haskell} labels, one with only the left child having a
 `'Just`{.haskell} label, and one with neither having `'Just`{.haskell} labels
 (why don't we need the fourth case?). This way, the heap property remains
 simple.

In a way, (1) and (2) are equivalent. One might say they are cleaner
than exploiting `'Z` being the least element in a total order. Both, however,
complicates every function that needs to scrutinise a `SaferHeap`{.haskell}.

The next step is to wrap the data type in an existential just like last time.

```haskell
data SomeSaferHeap = forall rank label. SSH' (SaferHeap rank label)
```

At this point, if we construct some `SaferHeap`{.haskell}s, we'd get bored
quickly due to constructing tedious explicit proofs. Luckily we use existentials
and `Heap`{.haskell} to interact with the data type.

## Heap instance for SaferHeap

Just as before the instance is for the existentially wrapped type.

```haskell
instance Heap SomeSaferHeap where
  type Elem SomeSaferHeap = Nat
```

The `Elem`{.haskell} instance for `SomeSaferHeap`{.haskell} is interesting
because we don't actually store `Nat`{.haskell}s anywhere. We store
`SNat`{.haskell}s instead. So `insert`{.haskell} requires a conversion from
`SNat`{.haskell} to `Nat`{.haskell} and `findMax`{.haskell} from `Nat`{.haskell}
to `SNat`{.haskell}.

The `SNat`{.haskell} to `Nat`{.haskell} direction is easy.

```haskell
demote :: SNat n -> Nat
demote SZ     = Z
demote (SS n) = S (demote n)
```

But the opposite direction would have a signature `Nat -> SNat n`{.haskell}.
Let's try to write that.

```haskell
promoteAttempt :: Nat -> SNat n
promoteAttempt Z                                = SZ
promoteAttempt (S n) | snat <- promoteAttempt n = SS snat
```

Well, this doesn't type check because one branch returns `SNat 'Z`{.haskell} and
the other `SNat ('S m)`{.haskell} for some `m`{.haskell}. Neither `'Z`{.haskell}
nor `'S`{.haskell} unifies with `n` in the signature.

Since our heap operations are on existentially wrapped types, we only need the
type-level `n`{.haskell} during the course of the function body but not in the
signature. So we do not really care what `n`{.haskell} is going to be so long as
there is _some_ `n`{.haskell} that we can embed in the heap. This sounds like an
existential. So the `promote`{.haskell} should return an existentially wrapped
`SNat`{.haskell}.

```haskell
data SomeNat = forall n. SomeNat (SNat n)

promote :: Nat -> SomeNat
promote Z                                 = SomeNat SZ
promote (S n) | SomeNat snat <- promote n = SomeNat $ SS snat
```

A good exercise is to implement `singleton` for `SomeSaferHeap`{.haskell}. It is
similar to that for `SomeSafeHeap`{.haskell}, except for the use
`promote`{.haskell} and the evidence for the heap property. See the source code
for the answer.

## Merging safer heaps

The merge operation is, once again, all we care about. The overall structure is
going to be the same, but we'll need more lemmas and plumbing.

### Making nodes

This time let's start from `mkNode`{.haskell}. Here's an attempt.

```haskell
mkNode :: Label c
       -> SomeSaferHeap -> SomeSaferHeap
       -> SomeSaferHeap
mkNode vc (SSH hA) (SSH hB)
  | rA <- rank hA, rB <- rank hB =
  case lemConnexity (_unRank rA) (_unRank rB) of
    Left  arLEQbr -> SSH $ Node'' vc (inc rA) hB hA arLEQbr ??? ???
    Right brLEQar -> SSH $ Node'' vc (inc rB) hA hB brLEQar ??? ???
```

This attempt fails due to a lack of evidence for the heap property.

We have the parent and the children labels, so we could decide on the evidence.
But this requires us to handle the case of `vc`{.haskell} being smaller than one
of the children labels. This should be established in the body of
`merge`{.haskell} if it is anything like the previous version. Let's assume
`merge`{.haskell} indeed passes down the evidence.

```haskell
mkNode :: Label c
       -> SomeSaferHeap -> SomeSaferHeap
       -> a <= c -> b <= c
       -> SomeSaferHeap
mkNode vc (SSH hA) (SSH hB) aLEQc bLEQc
  | rA <- rank hA, rB <- rank hB =
  case lemConnexity (_unRank rA) (_unRank rB) of
    Left  arLEQbr -> SSH $ Node'' vc (inc rA) hB hA arLEQbr bLEQc aLEQc
    Right brLEQar -> SSH $ Node'' vc (inc rB) hA hB brLEQar aLEQc bLEQc
```

This doesn't work either because we have an `a <= c`{.haskell} for the first
`SomeSaferHeap`{.haskell}, but that type hides `a`{.haskell}, so as far as the
type checker is concerned the rank of `hA`{.haskell} has nothing to do with
`Rank a`{.haskell}.

It seems we're hiding too much. Since `mkNode`{.haskell} is not part of the
`Heap`{.haskell} typeclass, perhaps we can use `SaferHeap`{.haskell} instead of
`SomeSaferHeap`{.haskell} in the signature of `mkNode`{.haskell}.

```haskell
mkNode :: Label c
       -> SaferHeap r1 a -> SaferHeap r2 b
       -> a <= c -> b <= c
       -> SaferHeap ??? c
```

This type signature relates the input heaps to the evidence, but it also
requires handling ranks. There are three viable choices for `???`{.haskell}:
`r3`{.haskell}, `'S r1`{.haskell}, and `'S r2`{.haskell}. The first one runs
into the same problem as `promote`{.haskell}, the calculated node rank won't
unify with `r3`{.haskell}. The last two can be made the work but it presupposes
that the call site already knows which heap is going to be the right child,
hence `mkNode`{.haskell} would be pointless.

So `SomeSaferHeap`{.haskell} hides too much and `SaferHeap`{.haskell} hides too
little. What we need is something in the middle to hide the rank, but expose the
label. Once again existential types come to the rescue.

```haskell
data AlmostSomeSaferHeap label = forall rank. ASSH (SaferHeap rank label)
```

With this, the `mkNode`{.haskell} we need is not too different from that for
`SomeSafeHeap`{.haskell}.

```haskell
mkNode :: Label c
       -> AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
       -> a <= c -> b <= c
       -> AlmostSomeSaferHeap c
mkNode vc (ASSH hA) (ASSH hB) aLEQc bLEQc
  | rA <- rank hA, rB <- rank hB =
  case lemConnexity (_unRank rA) (_unRank rB) of
    Left  arLEQbr -> ASSH $ Node'' vc (inc rA) hB hA arLEQbr bLEQc aLEQc
    Right brLEQar -> ASSH $ Node'' vc (inc rB) hA hB brLEQar aLEQc bLEQc
```

### Merging nodes

We'd like to work with `AlmostSomeSaferHeap`{.haskell} for the `merge`{.haskell}
implementation as well. In short, unless we do that the implementation doesn't
go through, but it is going to take some time to explain exactly why. For now,
bare with me.

Let's observe the use of the intermediary function `merge'`{.haskell} and its
type signature.

```haskell
merge (SSH' h1) (SSH' h2) | ASSH mergedHeap <- merge' (ASSH h1) (ASSH h2) =
  SSH' mergedHeap

merge' :: AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
       -> AlmostSomeSaferHeap (Max a b)
```

The type of `merge'` will be very precise. The label of a merge result is a
function of the labels of the inputs. Particularly, it is the maximum of the
input labels.

This brings me to type-level functions. We have already used associated type
families within the `Heap`{.haskell} and `HasRank`{.haskell} typeclasses, but
those are both simple maps of types. `Max`{.haskell}, on the other hand, needs
recursion!

#### Type families

The type-level `Max`{.haskell} function is defined using a closed type family
enabled by the `TypeFamilies` extension.

```haskell
type family Max (n :: Nat) (m :: Nat) :: Nat where
  Max 'Z m          = m
  Max n 'Z          = n
  Max ('S n) ('S m) = 'S (Max n m)
```

This is analogous to the following term level `max` function on
`Nat`{.haskell}s.

```haskell
max :: Nat -> Nat -> Nat
max Z m = m
max n Z = n
max (S n) (S m) = S (max n m)
```

You might be wondering why not just write that and get a promoted version of
`max`{.haskell} just as we did with data types and kinds? It's an excellent
question and this syntactic dichotomy is another reason why people don't like
type-level programming in Haskell. In Idris or Agda, that is exactly how it
works.

The problem is multifaceted. For one thing, type families existed in GHC since
2007, whereas data type promotion was added in 2012, and the mandate for moving
term and type levels closer is fairly recent. Further, adding type-level
computation into Haskell is an after-thought, so you need to retrofit the
syntax. On top of that, the behaviour of type families is different than
functions, the patterns of a type family can do unification whereas pattern
matches of a function can't.

For example, the following returns the type `Int`{.haskell} if its arguments
unify and `Char`{.haskell} otherwise.

```haskell
type family Same a b where
  Same a a = Int
  Same _ _ = Char

sameInt :: Same [ a ] [ a ]
sameInt = 42

sameChar :: Same (Maybe a) [ a ]
sameChar = 'c'
```

So although we can promote term-level functions to the type families
(`singletons` library does this via Template Haskell), they are not exactly
equivalent because term-level variables act differently than their type-level
counterparts.

I don't know what the current plan is, but since changing the behaviour of type
families would break backwards compatibility, the way forward is either to allow
unification at the term level or to create another extension that makes it
illegal at the type level. Since types heavily rely on unification, the latter
seems more likely to me, but I'm not an expert!

#### Type families vs GADTs

We could have encoded `Max`{.haskell} as a GADT as well and similarly we could
have encoded `(<=)`{.haskell} as a type family.

```haskell
data AltMax :: Nat -> Nat -> Nat -> Type where
  L ::                 AltMax n 'Z n
  R ::                 AltMax 'Z m m
  B :: AltMax m n r -> AltMax ('S m) ('S n) ('S r)

type family n <== m :: Bool where
  'Z     <== m      = 'True
  n      <== 'Z     = 'False
  ('S n) <== ('S m) = n <== m
```

These would have also worked. The proofs would have looked different and maybe
we would have used different lemmas, but they'd have worked. However, there are
reasons to choose one over the other.

 1. If you intend to do induction over your relation, then constructors are
 helpful, so GADTs get a point.

 2. If what you have is a function, then the GADT encoding forces you to add
 another type variable for the result and the functional dependency between the
 result and the arguments get lost.

 3. Conversely, if you have a relation that is not a function and you choose to
 use a type family, since there is no clear result variable, you need to return
 a type of kind `Bool`{.haskell} or its equivalent.

 4. With type families, when you learn more information about the type, the
 reduction happens automatically, whereas with GADTs you need to pattern match
 and pass the relation around.

 5. More pragmatically, you might already have some type-level relations in your
 codebase and you might want to stay consistent with the related relations.
 Beyond consistency, this might allow you to reuse some lemmas by exploiting
 duality and/or generalising the lemmas with minor effort.

My choices in this post embody the first three principles.

#### Getting back to the merge

We are ready to look at the base cases for `merge'`{.haskell}.

```haskell
merge' :: AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
       -> AlmostSomeSaferHeap (Max a b)
merge' (ASSH Leaf'') heap = heap
merge' heap (ASSH Leaf'') = heap
```

Pattern matches reveal the `Leaf''`{.haskell} labels as `'Z`{.haskell} to
the type checker. We need to show that `Max 'Z b`{.haskell} and `Max a
'Z`{.haskell}  are `b` and `a` respectively. These are proved definitionally
because `'Z`{.haskell} hits the base cases of `Max`{.haskell}.

In the previous version, term-level `(<=)`{.haskell} decided on the top
label and the spine to recurse on. We've already seen that
`lemConnexity`{.haskell} is the replacement we need for comparing
`SNat`{.haskell}s. By mimicking the structure of the previous implementation, we
can provide a partial implementation.

```haskell
merge' (ASSH hA@(Node'' vA@(Label sA) _ aLeft aRight _ lLEQa rLEQa))
       (ASSH hB@(Node'' vB@(Label sB) _ bLeft bRight _ lLEQb rLEQb)) =
  case lemConnexity sA sB of
    Left  aLEQb ->
      let child1 = ASSH bLeft
          c1LEQp = _
          child2 = merge' (ASSH bRight) (ASSH hA)
          c2LEQp = _
      in mkNode vB child1 child2 c1LEQp c2LEQp
    Right bLEQa ->
      let child1 = ASSH aLeft
          c1LEQp = _
          child2 = merge' (ASSH aRight) (ASSH hB)
          c2LEQp = _
      in mkNode vA child1 child2 c1LEQp c2LEQp
```

Let's focus on the `Left`{.haskell} branch first. The type checker complains
about the holes, but more importantly it complains about the `mkNode`{.haskell}
application. GHC says that it could not deduce `Max a b ~ b`{.haskell}, where
`~`{.haskell} means types are equal.

But of course! We have `aLEQb`{.haskell} of type `a <= b`{.haskell}, but the
type checker is too stupid to know that this implies `Max a b`{.haskell} is just
`b`{.haskell}. So we need to prove this. That brings us to _propositional
equality_.

#### Propositional equality

Let me introduce you to `(:~:)`{.haskell}, the data type that tells the type
checker that two types are equal. It took me ages to get my head around it. So
you have trouble with it, keep using it until it clicks.

```haskell
data (:~:) :: k -> k -> Type where -- Same as that in Data.Type.Equality
  Refl :: a :~: a
```

It is a poly-kinded `Type`{.haskell} constructor. Good that it is poly-kinded,
if it was restricted to `Type`{.haskell} or `Nat`{.haskell} that would restrict
which types we can show to be equal. This definition makes no assumptions.

If we pattern match on a term with type `a :~: b`{.haskell}, the only case is
the `Refl`{.haskell} constructor. Just like the previous pattern matches on
GADTs, this refines the typing context. In this case, it reveals `a` and `b` to
be the same (the signature for `Refl`{.haskell} says so). Hence, the type
checker learns `a ~ b`{.haskell}.

We need `Max n m ~ m`{.haskell} given `n <= m`{.haskell}, so we show `Max n m
:~: m`{.haskell}. We proceed by induction on `n <= m`{.haskell}.

```haskell
lemMaxOfLEQ :: n <= m -> Max n m :~: m
lemMaxOfLEQ Base = Refl
```

In the base case, the pattern match on `Base`{.haskell} reveals both
`n`{.haskell} and `m`{.haskell} to be `'Z`{.haskell}. So we need to show `'Z :~:
'Z`{.haskell}. We can use `Refl`{.haskell} by instantiating `a`{.haskell} to
`'Z`{.haskell} in `a :~: a`{.haskell} behind the scenes.

Then comes the first inductive case with `Double`{.haskell} constructor.

```haskell
lemMaxOfLEQ (Double xLEQy) | Refl <- lemMaxOfLEQ xLEQy = Refl
```

Here, `xLEQy`{.haskell} has type `n <= m`{.haskell} and we need to show `Max ('S
n) ('S m) :~: 'S m`{.haskell}. By definition of `Max`{.haskell}, the goal
reduces to `'S (Max n m) :~: 'S m`{.haskell}. Since `xLEQy`{.haskell} is smaller
than the original argument, we can recursively call `lemMaxOfLEQ`{.haskell} to
get a term of type `Max n m :~: m`{.haskell}.  Pattern matching on that tells
the compiler `Max n m ~ m`{.haskell}, so the goal reduces to `'S m ~ 'S
m`{.haskell}. Once again, `Refl`{.haskell} trivially proves this.

The last case was fairly mechanical and this is often the case.  The final
inductive case is more interesting.

```haskell
lemMaxOfLEQ (Single xLEQy) = _
```

The term `xLEQy`{.haskell} has type `n <= m`{.haskell} and we need to prove `Max
n ('S m) :~: 'S m`{.haskell}.  Since we don't know if `n`{.haskell} is built
with `'S`{.haskell} constructor (it could be `'Z`{.haskell}), we don't get an
automatic reduction of our goal like last time. We still have `xLEQy`{.haskell},
so we could apply `lemMaxOfLEQ`{.haskell} recursively. That would get us `Max n
m :~: m`{.haskell}, but pattern matching on that doesn't reduce the goal any
further.

The mechanical process got stuck. It's time to take a step back and think.
Taking inspiration from the previous case, if we knew that `n`{.haskell} was of
the form `'S k`{.haskell}, our goal would reduce to `'S (Max k m) :~: 'S
m`{.haskell}. Then we could show `Mak k m :~: m`{.haskell} and that would reduce
the overall goal to a measly `'S m ~ 'S m`{.haskell}. To obtain `Max k m :~:
m`{.haskell}, we need a recursive call to `lemMaxOfLEQ`{.haskell} with a term of
type `k <= m`{.haskell}, but we only have `'S k <= m`{.haskell}. Luckily we now
from grade school that $\vdash_{\mathit{PA}} k + 1 \leq m \implies k \leq m$. So
all we need is a lemma with type `'S n <= m -> n <= m`{.haskell}.

But we forgot something! This all hinges on `n`{.haskell} being of the form `'S
k`{.haskell}, what if it isn't?  Well, then it must be `'Z`{.haskell}, and `Max
'Z m :~: m`{.haskell} reduces to `m :~: m`{.haskell}, so we are good.

```haskell
lemMaxOfLEQ (Single xLEQy) =
  case fst $ recover xLEQy of
    SZ                                           -> Refl
    SS _ | Refl <- lemMaxOfLEQ (lemDecLEQ xLEQy) -> Refl
```

Alright, we can prove our final lemma.

```haskell
lemDecLEQ :: 'S n <= m -> n <= m
lemDecLEQ snLEQm = uncurry go (recover snLEQm) snLEQm
  where
  go :: SNat ('S n) -> SNat m -> 'S n <= m -> n <= m
  go _            SZ     _            = error "Impossible case."
  go _            (SS _) (Single leq) = Single (lemDecLEQ leq)
  go (SS SZ)      y      (Double _)   = lemZLEQAll y
  go (SS (SS _))  (SS _) (Double leq) = Double (lemDecLEQ leq)
```

There is nothing particularly difficult about this lemma apart from the number
of arguments the induction involves, but it has some lessons.

Haskell doesn't have a termination checker. This is a feature, but when we do
proofs, it feels like walking barefoot right after breaking a glass. We can
easily create an infinite loop that type checks but does not constitute a valid
proof (the circular argument fallacy).

This proof is particularly vulnerable to accidental loops because we pattern
match on three variables which makes it difficult to see that we are recursing
on something smaller in every case.

We remedy this in `lemDecLEQ`{.haskell} by making the recursive calls in the
body of `go` to `lemDecLEQ`{.haskell} rather than `go`{.haskell} itself. This is
less efficient, but makes it easier to confirm that each recursive call is to
something strictly smaller than what we started with.

The other interesting bit is the base case of `go`{.haskell}.

```haskell
go :: SNat ('S n) -> SNat m -> 'S n <= m -> n <= m
go _ SZ _ = error "Inaccessible case."
```

We use `error` due to a deficiency of Haskell. When the second argument is
`SZ`{.haskell}, there is no constructor of `(<=)`{.haskell} that can make `'S n
<= m`{.haskell}, but we have a proof of this, namely the third argument. We can
see this by pattern matching on the third argument.

```haskell
go :: SNat ('S n) -> SNat m -> 'S n <= m -> n <= m
go _ SZ Base     = undefined
go _ SZ Single{} = undefined
go _ SZ Double{} = undefined
```

If you compile this, GHC will give you pattern match inaccessible warnings
combined with type errors about why these arguments can't coexist together.

In Agda and Idris, you can syntactically make it an inaccessible case which the
compiler can confirm or deny. In Idris, it looks like this:

```haskell
go _ SZ _ impossible
```

We don't have this in Haskell, but there is a
[proposal](https://gitlab.haskell.org/ghc/ghc/issues/10756#comment:4). What if
we omit this case altogether? This leads to a non-exhaustive pattern match
warning because only when we pattern match on the second argument GHC learns
that the pattern is inaccessible.

This is dangerous because we might prove a lemma, tweak it slightly, and not
realise that the inaccessible case is now perfectly accessible. The case would
type check fine because we have `error "Inaccessible case"`{.haskell}. This
makes the proof incomplete at best, wrong at worst if there is no way of
handling the case.

#### Getting back to the merge again

Focusing on the `Left`{.haskell} branch only, we make it known to the compiler
that `a <= b`{.haskell} implies `Max a b ~ b`{.haskell} using
`lemMaxOfLEQ`{.haskell}.

```haskell
merge' (ASSH hA@(Node'' vA@(Label sA) _ aLeft aRight _ lLEQa rLEQa))
       (ASSH hB@(Node'' vB@(Label sB) _ bLeft bRight _ lLEQb rLEQb)) =
  case lemConnexity sA sB of
    Left  aLEQb | Refl <- lemMaxOfLEQ aLEQb ->
      let child1 = ASSH bLeft
          c1LEQp = _
          child2 = merge' (ASSH bRight) (ASSH hA)
          c2LEQp = _
      in mkNode vB child1 child2 c1LEQp c2LEQp
    Right bLEQa -> ...
```

This gets rid of the type error due to the application of `mkNode`{.haskell}.

Inspecting the errors for the holes should inform us about the terms we need.
Well, according to GHC, both holes demand type `t`{.haskell} (distinct rigid
`t`{.haskell}s). This is incredibly unhelpful and I don't why we get
`t`{.haskell}.

Inlining the `let` binding yields better results.

```haskell
mkNode vB (ASSH bLeft) (merge' (ASSH bRight) (ASSH hA)) _ _
```

The first hole needs a term of type `l <= b` and that's exactly the type of
`lLEQb`. The second hole needs `Max r a <= b`, but we do not yet have a term
corresponding to this type. However, we have `rLEQb :: r <= b` and `aLEQb :: a
<= b`. Since `Max` is a selective function, the required result holds we just
need to turn it into a lemma.

```haskell
lemDoubleLEQMax :: n <= l -> m <= l -> Max n m <= l
lemMaxSelective :: SNat n -> SNat m -> Either (Max n m :~: n) (Max n m :~: m)
```

The proofs are left as exercises and the solutions are in the source code.

We can now give the full definition of the `Left`{.haskell} branch.

```haskell
Left  aLEQb | Refl <- lemMaxOfLEQ aLEQb ->
  let child1 = ASSH bLeft
      c1LEQp = lLEQb
      child2 = merge' (ASSH bRight) (ASSH hA)
      c2LEQp = lemDoubleLEQMax rLEQb aLEQb
  in mkNode vB child1 child2 c1LEQp c2LEQp
```

The right branch is analogous to the left one, so you should be able to fill it
yourself. There is going to be a technicality requiring a simple lemma that is
not required in the `Left`{.haskell} branch because of the way we set things up.
If you write the `Right`{.haskell} as we did `Left`{.haskell}, the type error
should give you a clue about what is needed. If you can't figure it out, that
too is in the source.

#### Other operations?

We could implement the other methods, but they are all too simple. We are done!
No more verification.

# Simulating heap operations

So after going through all this trouble to prove properties of our code, why
bother testing?

 1. We didn't verify everything. Earlier we gave the example of implementing
 `singleton`{.haskell} with the wrong rank by ignoring the input. A common theme
 is to accidentally discard a subpart of a data structure or an input and use
 another part twice.

 2. Haskell's type system is unsound. So we might have a fallacious proof
 somewhere that makes it look like the property holds while being buggy.

 3. It gives me a chance to talk about another type-level feature: visible type
 applications.

 4. I really want to use QuickCheck to run simulations on the heap.

It is worth noting that if Haskell had [linear types]() ([it soon will!]()), we could
have addressed (1) by forcing inputs to be used.

## Generating actions

We're only going to simulate insertion and deleting the min. Here's the initial
encoding of the actions.

```haskell
data Action a = Insert a | DeleteMax deriving Show
```

Let's give `Arbitrary`{.haskell} instances for `Nat`{.haskell} and
`Action`{.haskell} to randomly generate sequences of `Action`{.haskell}s.

```haskell
instance Arbitrary Nat where
  arbitrary = fromInt . getNonNegative <$> arbitrary @(NonNegative Int)
    where
    fromInt 0 = Z
    fromInt n = S (fromInt (n - 1))

instance Arbitrary a => Arbitrary (Action a) where
  arbitrary = do
    shouldAddInsert <- arbitrary @Bool
    if shouldAddInsert
      then Insert <$> arbitrary
      else pure DeleteMax
```

Somewhat arbitrarily we choose between a deletion and an insertion with $50%$
probability. This may or may not be a realistic simulation, but it is something
easy to adjust. You could have multiple wrappers over `Action a`{.haskell} such
as `DeleteHeavy a`{.haskell} and `InsertionHeavy a`{.haskell} to simulate
different scenarios.

We haven't seen the `@`{.haskell} symbols in the `Arbitrary`{.haskell} instances
before. They are visible type applications via `TypeApplications` extension.  In
addition to drastically improving handling ambiguous types, they are allow me to
show what type variables truly are in Haskell.

### There is $\Lambda$ then there is $\lambda$

If someone asks for the explicitly-typed polymorphic lambda term for the
identity function (as one does), we'd probably write $\lambda x : \alpha. x$,
where $\alpha$ is a polymorphic type variable. We'd expect this function to be
closed, that is to say it shouldn't depend on the context. Indeed, our identity
function looks unaffected by the term-level context because the only variable
$x$ is $\lambda$ bound. However, $\alpha$ doesn't seem to be bound by anything,
hence it looks dependent on the context.

Appearances can be deceiving. If this term should be interpreted as Haskell
interprets terms and their signatures, it just abbreviates $\Lambda \alpha :
\mathit{Type}. \lambda x : \alpha. x$. All free type variables in signatures are
implicitly $\Lambda$ bound. The Haskell syntax is `forall` and is only allowed
in signatures (with `ExplicitForAll` enabled).

The following is the same identity function in Haskell but with explicit
quantification.

```haskell
id :: forall (a :: Type). a -> a
id x = x
```

Just as the binders are hidden behind the scenes, so are the applications.  When
we apply `id`{.haskell} to `42`{.haskell}, the `Int`{.haskell} gets passed to
the type-level function first. `TypeApplications` enables syntax to do this
explicitly. You just pass the type with a `@` prefix.  For example in `ghci`,
`:t id @Int` yields `Int -> Int`{.haskell}.

This works as an alternative to using `::`{.haskell} when a type is ambiguous.
Often it lets us get away with fewer parentheses and looks cleaner in general.

What happens if there are multiple type variables? The applied type is unified
with the first type variable. This is how term-level application works as well.
This raises the question type variable ordering.

In the absence of an explicit `forall`{.haskell}, the ordering of type variables
is up to GHC. We can query the order of type variables used by GHC via `:type
+v` and `-fprint-explicit-foralls` flag. However, I think placing explicit
`forall`{.haskell}s is good practice.

We look at type applications more interesting than those in the
`Arbitrary`{.haskell} instances momentarily.

## Executing actions

We can now interpret the initial representation of our actions. Nothing exciting
here.

```haskell
execAction :: Heap heap => Action (Elem heap) -> heap -> Maybe heap
execAction (Insert x) = Just . (x `insert`)
execAction DeleteMax  = deleteMax

carryOutActions :: Heap heap => [ Action (Elem heap) ] -> Maybe heap
carryOutActions = foldlM (flip execAction) empty
```

## QuickChecking functional equivalence

It's time to use QuickCheck. The desired property: given two data types
implementing `Heap`{.haskell} and a series of actions, executing these actions
on the `empty`{.haskell} of each should yield the same maximum.

```haskell
sameMaxAfterActions :: forall heap heap'
                     . Heap heap => Heap heap'
                    => Elem heap ~ Elem heap'
                    => Eq (Elem heap)
                    => [ Action (Elem heap) ] -> Bool
sameMaxAfterActions acts =
  maxOfActions @heap acts == maxOfActions @heap' acts
  where
  maxOfActions :: forall h . Heap h
               => [ Action (Elem h) ] -> Maybe (Maybe (Elem h))
  maxOfActions = fmap findMax . carryOutActions @h
```

The computation is not very interesting, but the way we direct it is.  We use an
explicit `forall`{.haskell}. This is not to fix the type variable ordering.
Since both `heap`{.haskell} and `heap'`{.haskell} are passed to the same
function, the ordering is irrelevant. `ScopedTypeVariables` extension allows
`forall`{.haskell} quantified type variables to be referenced in the function
body which we need to pick the implementation `maxOfActions`{.haskell} should
use.

The type applications `@heap`{.haskell} and `@heap'`{.haskell} determine the
computation. This is not just disambiguation. If both `maxOfActions` were
applied to `heap`{.haskell} instead, we'd create a property that is trivially
satisfied.

We use another type application in the body of `maxOfActions`{.haskell}. This is
for disambiguation. Without it, all `carryOutActions` sees is `Elem
h`{.haskell} and `Elem`{.haskell} isn't injective. This means given `Elem
h`{.haskell}, we can't know what `h` is. For example, if I told you `Elem
h`{.haskell} was `Int`{.haskell}, `h` could be `LeftistHeap`{.haskell} or
`SomeSafeHeap`{.haskell} as both can have `Int`{.haskell} labels. Hence, we use
the type application to tell `carryOutActions`{.haskell} what `h` is.

All there remains is to actually check the property between different
implementations.

```haskell
main :: IO ()
main = do
  quickCheck (sameMaxAfterActions @(LeftistHeap Int)  @[ Int ])
  quickCheck (sameMaxAfterActions @(SomeSafeHeap Int) @[ Int ])
  quickCheck (sameMaxAfterActions @SomeSaferHeap      @[ Nat ])

  putStrLn ""
  sampleActions <- sample' (arbitrary @(Action Int))
  print sampleActions
  print $ carryOutActions @[ Int ] sampleActions
```

Remember that the list based heap implementation was our reference
implementation. Using type applications, we test functional equivalence between
the reference implementation and the untyped leftist heap, the leftist
property verified leftist heap, and the leftist and heap property verified
leftist heap.

Then I just sample some actions and see the result of carrying them out on the
terminal because I'm paranoid like that (the `Arbitrary`{.haskell} instance
could also be buggy 🙃).

At this point, we can be reasonably sure that these implementations work (at
least for insertion and deletion).

# Conclusion

After such a long post, I'll keep the conclusion short and sweet. Here's what we
did in a gist:

 - learnt about leftist heaps a purely functional replacement to array-based
   binary heaps;
 - looked at all major parts of Haskell's type-level computation features;
 - ran simulations to test functional equivalence of various implementations;
 - did a commentary on Haskell as an interactive theorem prover.

What is the overall verdict on that last point? It's not ideal at all, but it
works for simple data structures and properties. If we had used the `singletons`
library and type-checker plugins, we could have gone further quicker.

The often overlooked point is this: if we want to do verification natively in a
language that is designed to build programs with an optimising compiler and a
massive ecosystem, Haskell is the singular choice. I for one am looking forward
to Haskell's typed and bright future.

## Acknowledgements

I'd like to thank Dr Dominic Orchard and Lex van der Stoep for their comments.

This post wouldn't be possible without the heroic work of a vibrant research
community and GHC implementers. They are too many to name exhaustively, but the
following deserves a special round of applause: [Dr Richard
Eisenberg](https://richarde.dev/index.html) and [Prof. Stephanie
Weirich](https://www.cis.upenn.edu/~sweirich/) ([closed type
families](https://dl.acm.org/citation.cfm?id=2535856),
[singletons](https://dl.acm.org/citation.cfm?id=2364522)), [Dr James
Cheney](https://homepages.inf.ed.ac.uk/jcheney/)
([GADTs](https://ecommons.cornell.edu/handle/1813/5614)), and [Dr Hongwei
Xi](https://www.cs.bu.edu/~hwxi/) ([also
GADTs](https://dl.acm.org/citation.cfm?id=604150)).

The code wouldn't be as slick if it wasn't for Prof. Weirich's presentations on
[verifying red-black trees](https://www.youtube.com/watch?v=n-b1PYbRUOY)
([alternative](https://www.youtube.com/watch?v=rhWMhTjQzsU)).
