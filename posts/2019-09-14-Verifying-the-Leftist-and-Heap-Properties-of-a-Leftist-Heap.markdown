---
title: Verifying Leftist and Heap Properties of a Leftist Heap
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
[...]". It downed on me that I remember the heap property and heap interface,
but not how to implement it. I was horrified when I remembered despite
conceptually being a tree, binary heaps are implemented using arrays. Despite
having used Haskell as my primary language, decided to implement it in Ruby---my
prior primary language. After some time and indexing errors later, I got it
working. Then ported it to Haskell's using the [`ST`
monad](http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Monad-ST.html).
After writing `STRef` one too many times, I got that working too, but it left
much to be desired. "Save the trees" yelled my terminal!

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
 - [A leftist heap](#a-leftist-heap) describes a datatype for leftist heaps
   without using fancy types and discusses the asymptotic complexities of its
   operations;
 - [Terms, types, and kinds](#terms-types-and-kinds) covers the basic entities
   in modern Haskell and how they relate to each other. Type-level features:
   datatype promotion and kind polymorphism;
 - [Verifying the leftist property](#verifying-the-leftist-property) explains
   the datatype encoding the leftist property and the implementation of its
   property preserving operations. Type-level features: generalised algebraic
   data types, singletons, kind signatures through the example of [natural
   numbers](#natural-numbers), and existential types through [the heap instance
   for our datatype](#heap-instance-for-safeheap). We also introduce [theorem
     proving](#comparing-without-forgetting) in Haskell.
 - [Verifying the heap property](#verifying-the-heap-property) encodes both the
   leftist and the heap properties into a datatype. Most of this section is on
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

The exposition of the code is fragmented and out of order, but I provide the
well-organised source code at [the very end of the post](#full-program). We
won't use any libraries except
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

  -- Motification
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

This typeclass is a bit mouthful because many operations are inter-definable as
reflected in the `MINIMAL` pragma.

The `Elem` type-family (enabled by `TypeFamilies`) associated with the class
gives the type of the element of that heap. It is nothing but a function from
types of containers to types of their elements. We could have equally used
`MultiParamTypeClasses` and `FunctionalDependencies` extensions to establish the
same container-element relationship. Because I will be using type families in a
moment for different reasons anyway and because I find that `Elem heap` has less
cognitive overhead than remembering functional dependencies between type
variables, I opted for a type-family here.

Although `insert`, `findMax` and `deleteMax` are probably the most used
operations of the interface, `merge` is the one that we care about the most. The
default implementations in the typeclass gives a hint why. The `isEmpty`
predicate, `findMax`, `singleton`, and `empty` are all trivial to implement for
all data structures we use as heaps today. Then with `merge`, we can implement
`insert`, `fromList`, `decompose`, and `deleteMax`.

Before implementing this interface for a leftist heap, let's look at a much
simpler implementation of a heap using lists.

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

This is possibly one of the easiest heap implementations. Insertion is $O(1)$,
merging is $O(n)$, conversion from a list is $O(1)$, decomposing (and
subsequently finding and deleting the maximum) is $O(n)$. If it wasn't for that
last linear time complexity, it would have been a perfectly fine heap
implementation, alas here we are.

This implementation is _obviously_ correct. As such any other correct heap
implementation should be _functionally equivalent_ to it. That is to say if we
perform the same heap operations on two implementations holding the same set of
elements, the maximum of both heaps should be the same. Then this obviously
correct heap implementation is useful for [testing other heap implementations by
way of simulation](#simulating-heap-operations).

# A leftist heap

Since we'll go through the trouble of implementing leftist heaps multiple
times, let's spend a second on comparing it to array-based binary heaps.

Why bother with the leftist heap? It is persistent (hence better suited for
multi-threaded computation), purely functional, both conceptually and
implementation-wise a tree, and more resilient against off-by-one errors. Why
bother with the array-based binary heap? Its operations are in place; it
probably performs better in practice because arrays tend to have good locality
of reference (this is a hunch, I haven't actually looked at its cache behaviour
and I'd like to be proven wrong); it is the best-known implementation, so easier
to communicate.

We can also look at their complexities more concretely. Leftist heaps have
$O(\lg{n})$ complexity for insertion and deleting the maximum, while
maintaining $O(1)$ complexity for finding the maximum. Building a heap out of a
`Foldable` collection is $O(n)$. So far we're on par with binary heaps. But we
can do one better. While merging binary heaps is $O(n)$, it's only $O(\lg{n})$
for leftist heaps. In fact, this is the reason why insertion and deleting the
maximum are $O(\lg{n})$.

## The data structure and its properties

We now look at the data structure. A leftist heap is is implemented as a tree.
We use the following familiar data type for the unverified implementation.

```haskell
data LeftistHeap a = Leaf | Node a Int (LeftistHeap a) (LeftistHeap a)
```

The tree structure is standard. The difference is the `Int` parameter of nodes.
This is the _rank_ of the tree. The rank of the tree is the least distance to a
`Leaf` node. The rank of a `Leaf` node is 0 and rank of a `Node` is the minimum
of its children ranks plus 1.

Let's briefly look at the relationship between the size of a tree and its rank.

A first question is how many elements there needs to be in the tree if its rank
is $R$?  If you want to figure this out for yourself, stop reading now. If the
rank of a tree is $R$, then it must be the case that each path from the root has
$R$ `Node`s, otherwise the rank of the tree would be fewer. This means the tree
has at least $2^{R} - 1$ elements.

Then the followup question is, if a tree has $N$ elements, what is its maximum
rank? This is the place to stop to figure out on your own. Well, we know that
the rank imposes a lower bound on the tree size, so conversely, the tree size
should impose a maximum on the rank. If $R$ is the maximum rank, we have $2^{R}
- 1 \leq N \lt 2^{R + 1} - 1$, so $R \leq \left\lfloor{\lg{(N + 1)}}
\right\rfloor < R + 1$. Hence, $\left\lfloor{\lg{(N + 1)}} \right\rfloor$ is
the desired maximum.

The leftist heap, in addition to this tree structure and the heap property, has
the _leftist property_. The rank, $R$, of a given node is the distance from
that root to the right-most `Leaf`. Consequently, since each subtree in a
leftist heap is also a leftist heap, the rank of any left child is at least as
big as that of the right child, hence the name.

How can we refine the statement about the maximum rank for leftist heaps? Stop
reading to figure out for youself. The distance between the root and the
right-most `Leaf` is $\left\lfloor{\lg{(N + 1)}} \right\rfloor$, if the leftist
heap has $N$ elements in it. This is the critical information we'll use to
derive the complexity of the `merge` operation.

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

The instance for the `LeftistHeap` is as follows. We need the `Ord` constraint
on the elements for the heap property and the element of a `LeftistHeap a` is
`a`. The necessary operations are implemented over the next two sections.

```haskell
instance Ord a => Heap (LeftistHeap a) where
  type Elem (LeftistHeap a) = a
```

## Merging two heaps

Let's tackle the most important operation head-on. The base cases are simple as
`Leaf` acts as the identity element for `merge`.

Now here's the for the idea for the recursive case: we want to walk over the
right-most paths of the input heaps. You can see this in the recursive calls
below; they only make use of the right children of one heap and the other one
untouched.

We recurse on the right child of the argument heap with the bigger label at its
root. This preserves the heap property.

To build the new node we use `mkNode` helper rather than `Node` constructor
directly. The helper does two things. First, it calculates the new rank which is
one more than the rank of the right child. Second, it makes the child with the
lowest rank the right child of the new node. Since the arguments to `mkNode` are
leftist heaps themselves, this flip ensures the right-most path to `Leaf` is
still the shortest.

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

Now what is the complexity of this? At each recursive call we potentially do a
flip, increase the rank, and construct a tree node, these are all constant time
operations. So the question is how many recursive calls there are. If the
leftist heaps being merged have $L$ and $R$ elements inside, we know their right
spines are at most length $\left\lfloor lg{(L + 1)}\right\rfloor$ and
$\left\lfloor lg{(R + 1)}\right\rfloor$ respectively. Hence, we at most do
$\left\lfloor\lg{(L + 1)} + \lg{(R + 1)}\right\rfloor$ calls. So the overall
complexity is $O(\lg{(L \times R)})$ which is a subset of $O(\lg{(L + R)})$ (can
you see why?). In other words, the merge operation is logarithmic in the size of
the merged heaps.

But this is not where the beauty of the merge ends. Recall that most of the
elements of the leftist tree live in trees outside right-most spine and we never
touch them, just move them around without deconstructing. In a purely functional
language, this means that we can share those trees in the merged tree with the
input trees.

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

From `merge` follows everything else. Maximum is maintained at the root, so
accessing it is easy. The `decompose` operation returns the maximum along with
the rest of the heap with the maximum removed. It accesses the root and merges
its two children. Insertion (the default implementation) creates a singleton
heap out of the inserted label and merges it into the heap.

Since `merge` has logarithmic complexity, so does `insert` and `deleteMax`.
Since we store the maximum at the root, `findMax` runs in constant time.

Conversion from a list is more interesting. The obvious implementation is to
fold over the list of elements and insert them into the heap, this turns out not
to be the most efficient way. If we instead turn each element into a singleton
heap and repeatedly merge two heaps at a time (with multiple passes) until one
heap is left, conversion happens in linear time. The following is the default
implementation given in the typeclass.

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

If you want to figure out why that is for youself this is the place to stop.
Assume for simplicity that there are $2^R$ elements. Then in the first pass we
do $2^{R-1}$ $O(\lg{2})$ operations. In the next pass, we do $2^{R-2}$
$O(\lg{4})$, then $2^{R-3}$ $O(\lg{8})$ operations and so on. So the overall
complexity is $O(\sum^{R}_{i = 1}{(\lg{2^i}) 2^{R-i}}\,)$ which is
$O(\sum^{R}_{i = 1}{i \; 2^{R-i}}\,)$ and that is $O(2^{R})$.  That is the
number of elements we started with, so conversion from list is done in linear
time.

# Terms, types, and kinds

Before verifying anything with types, we need to understand terms, types, and
kinds in Haskell. Haskell imposes a separation of the term and the type levels.
Here's the conceptual gist: all terms have types, all types have kinds, and
there is no distinction between types and kinds since GHC 8.0.

For example, just as you can say `42 :: Int`, you can also say `Int :: Type` (or
its synonym `Int :: *`, import `Data.Kind` for the more descriptive synonym
`Type`) and `Type :: Type`. We can read these has the term `42` has type `Int`,
the type `Int` has kind `Type`, and the kind `Type` has kind `Type` (yup, not a
typo).

I'll give more detail about these in the rest of this section. It may be too
much information to soak in at once, but the broad-strokes should be enough for
this post. More generally, one can get away without an in-depth understanding of
these and still be able to verify data structures, but then we'd be relying on
GHC to yell at us when certain extensions are missing and not understand why
we're being yelled at.

If you are worried about `Type :: Type`, yes, it is problematic and it leads to
[Russel's paradox](https://en.wikipedia.org/wiki/Russell%27s_paradox). This is
one reason, people don't like type-level programming in Haskell. It means as a
proof system, Haskell's type system is inconsistent. What that means is that _we
don't have the ability to tell the truth_. If you have a type-level proof of
something and your type checker confirms it, it might just be a lie. However,
since Haskell is not total and `let x = x in x`, `undefined`, and `error "QED"`
already inhabit **every** type. So fallacious types representing propositions
already have inhabitants meaning we didn't have the ability to tell the truth to
start with. So we are not worse off with `Type :: Type`. However, it is still
icky and it means the degree of trust you can place on an Agda proof and a
Haskell proof are different.

Now that we got that technicality out of the way, we can look at more
interesting kinds. The constructor `(:)` has type `a -> [a] -> [a]`, similarly
the type `Either` has kind `Type -> Type -> Type`. This makes sense because just
as `(:)` constructs a term out of an `a` and a `[a]`, `Either` constructs a type
out of two `Type`s. `Either` is a type constructor. In `ghci`, you can use `:t`
to query the type of a term and `:k` to query the kind of a type.

`Type` is the kind of inhabitable types, meaning types that have terms
associated with them, meaning if we have type `T :: Type`, then there can
potentially be a term `t :: T`. The previous sentence lacks certainty because
there are some types despite having the kind `Type` does not have any
inhabitants. For example, the type `Void` from `Data.Void` has no inhabitants.
If you declare a type `data T` without any constructors, that also has no
inhabitants. However, if a datatype does have an inhabitant, then it definitely
has kind `Type`.

The other sort of kinds that we have seen are type constructors such as
`Either`, `Maybe`, or `[]`. But those are a bit boring, there are more to kinds
than facilitating production of inhabitable types. With the `DataKinds`
extension, we can create new kinds that have nothing to do with `Type` and are
therefore not inhabitable.

Consider the following `List` declaration.

```haskell
data List a = Nil | Cons a (List a)
```

In vanilla Haskell, this generates a type `List` and two data constructors `Nil`
and `Cons`.

```haskell
List :: Type -> Type
Nil  :: List a
Cons :: a -> List a -> List a
```

With `DataKinds` extension enabled, you also get following.

```haskell
'Nil  :: List a
'Cons :: a -> List a -> List a
```

Despite having precisely the same names and looking awfully similar, these are
different beasts. Since there is no distinction between types and kinds, the
type constructor `List` is also a kind constructor. Then, `'Nil` and `'Cons` are
type constructors. Is there a term `t` with `t :: 'Cons Int 'Nil`? No, there
isn't because the kind of `'Cons Int 'Nil` is `List Int` which is distinct from
`Type` and since only `Type` is inhabitable, there is no such `t`.

This promotion feature alone spawns multiple reasons why people do not like
fancy types in Haskell:

  1. The `'` prefix of promoted type-constructors is optional, but terms and
  types are completely separate. So when I type `Nil`, GHC figures out whether
  it is a term or a type constructor depending on the context.

  2. The built-in list type `[a]` is automatically promoted. This means there is
  `[]` which the equivalent of `Nil`. There is `[]` which is the type and kind
  constructor equivalent to `List`. There is `'[]` which is the type constructor
  euivalent to `'Nil`. Remember that `'` is optional. So when I use `[]`, we
  don't know, if it is the type constructor `List` or the type constructor
  `Nil`. Call me crazy, but this is confusing. Similar situation occurs with
  tuples, where the term and type syntax are the same.

At the term level we talk about polymorphic types such as `reverse :: [a] ->
[a]`. You guessed it right, types can be poly-kinded. In fact, the `'Cons` type
constructor has kind `a -> List a -> List a` where `a` is a kind variable. We
can see this in `ghci`. If you type `:k 'Cons Int`, you get `'Cons Int :: List
Type -> List Type`, but if you type `:k 'Cons Maybe`, you get `'Cons Maybe ::
List (Type -> Type) -> List (Type -> Type)'` instead. In fact, you can use a
promoted kind as well: `:k 'Cons 'Nil' gives `'Cons 'Nil :: List (List a) ->
List (List a)`.

How about the kind of the type constructor `List`? `:k List` returns `Type ->
Type`. The return kind makes sense, it's a type constructor after all, but what
is the reason for the input `Type`? If you look at the `Cons` data constructor,
it has the type `a -> List a -> List a`, that first `a` is why the argument to
`List` has to be `Type` because constructing a term `Cons x xs` means there is a
term with `x :: a`, hence `a` must be inhabitable meaning it has to be `Type`.

But what about the following datatype?

```haskell
data Proxy a = ProxyC
```

If we ask `ghci` for the kind of `Proxy`, we get `Type -> Type` again, but this
time `a` does not appear as a type parameter to the sole constructor `ProxyC`.
So in principle, the kind of `Proxy` could be `k -> Type` where `k` is a kind
variable. This is another instance of poly-kindedness. GHC, by default, assumes
that the type variables of a type constructor have the kind `Type` even if they
can be more generic as is the case with `Proxy`. If you turn on the `PolyKinds`
extension, GHC correctly assigns the kind `k -> Type` to `Proxy`. Later in the
post, we define an equality type which has to be poly-kinded and which nicely
illustrates the use of poly-kindedness.

With this, you have a good bird's-eye view of Haskell types.

# Verifying the leftist property

Let's encode the leftist property at the type level. That is, we will ensure
that each the rank of each right child of a node is less than or equal to the
rank of its left child. Clearly, for this we need ranks at the type-level. Our
previous implementation used `Int`, but we really just need natural numbers. If
what we need is type-level natural numbers, we have two options:

1. Import `GHC.TypeLits`, which uses compiler magic to define a `Nat` _kind_
   where integer literals can be used at type-level.
2. Define a `Nat` kind inductively.

The advantage of (1) is it is efficient and most things we need are already
proved for us. The advantage of (2) is that it is not compiler magic and we get
to see how theorem proving and faking dependent types in Haskell work in action.
Hence, we'll do (2).

Note that if you try to reproduce this implementation using (1), you should
probably use the [`singletons`
library](http://hackage.haskell.org/package/singletons) to fake dependent types
and the fantastic GHC type checker plugin
[`ghc-typelits-natnormalise`](http://hackage.haskell.org/package/ghc-typelits-natnormalise-0.7)
to prove theorems about natural numbers. The cost of using efficient natural
numbers is to give up the inductive definition which means proving things by
hand is difficult.

Here's the plan. We first invent natural numbers and $\leq$. Then we forget
about the operations on heaps and try to represent the data structure
adequately. Then we attempt to define `merge` on our instance and fail. At which
point we provde some lemmas about natural numbers, then try to implement `merge`
again and succeed.

## Natural numbers

We need the type-level natural numbers and $\leq$ relation between them. So
let's define them.

```haskell
data Nat = Z | S Nat deriving (Eq, Show)
```

This gives us a type and a kind `Nat`, data constructors `Z :: Nat` and `S ::
Nat -> Nat` and type constructors `'Z :: Nat -> Nat` and `'S :: Nat -> Nat`.

### GADTs

Good, we have type level natural numbers, now we need the `<=` relation. To
define that, we'll need Generalised Algebraic Data Types (GADTs) enabled via
`GADTs` extension. This gives us an alternative syntax for declaring data types
and the ability to discriminate types based on constructors. The `Nat` data type
above can be translated to the GADT syntax with exactly the same semantics.
You'd need also need the `KindSignatures` extension to make the optional kind
annotation next to `Nat` work.

```haskell
data AnotherNat :: Type where
  AZ ::               AnotherNat
  AS :: AnotherNat -> AnotherNat
```

This is just a more verbose way of defining `Nat`. GADTs flex their muscles,
when they encode useful information in a type. Consider the following variant on
natural numbers which encode whether the number is zero or not at the
type-level.

```haskell
data Zeroness = DefinitelyZero | NonZero

data TaggedNat :: Zeroness -> Type where
  TZ ::          TaggedNat 'DefinitelyZero
  TS :: Nat a -> TaggedNat 'NonZero
```

What this says is that if you choose the constructor `TZ`, you'll get a natural
number tagget with `DefinitelyZero`, if you use the `TS` constructor regardless
what kind of natural is passed to it, you get a `NonZero` natural number.

This is useful because then we can write a total function a `div :: TaggedNat a
-> TaggedNat NonZero -> TaggedNat a` and types ensure that you won't divide by
zero.

For the purposes of this post, we don't actually need naturals keeping track of
whether their "zeroness". The vanilla data type declaration works fine, but
introducing `(<=)` as a first `GADT` is just mean.

### Less than or equal to relation

With `TypeOperators` enabled to use infix operators at type level, we can define
`(<=)`.

```haskell
data (<=) :: Nat -> Nat -> Type where
  Base   ::             'Z <= 'Z
  Single :: n <= m ->    n <= 'S m
  Double :: n <= m -> 'S n <= 'S m
```

What does this say? We are defining a relation that takes two `Nat`s, so far so
good, and it produces a data type, which might sound a bit weird. Isn't it more
natural to produce a type of kind `Bool` to say whether it holds or not?  Well,
we could do that using type families (a similar example will follow later on).
But this GADT encoding of the relation (which has to produce kind `Type`)
records a series of steps that gets us to the desired $n \leq m$ from an
indisputable fact.

The indisputable fact is $0 \leq 0$ encoded by the `Base` constructor, then by
wrapping it with a series of `Single`s and `Double`s, we try to produce the
desired inequality $n \leq m$. `Single` and `Double` encodes the following
mathematical statements $n \leq m \implies n \leq m + 1$, and $n \leq m \implies
n + 1 \leq m + 1$. Hopefully, neither are controversial as our verification claims
hinge on these being sound.

For example, to establish $1 \leq 2$ we need to give a term of the type `'S 'Z
<= 'S ('S 'Z)`.

```haskell
oneLEQtwo :: 'S 'Z <= 'S ('S 'Z)
oneLEQtwo = Single $ Double $ Base
```

that is to say from $0 \leq 0$, we can get to $1 \leq 1$, and from there we can
get to $1 \leq 2$.

Soundness is one question and _completeness_ is another. Is it the case that
by applying `Single` and `Double` to `Base`, you can get to any $n \leq m$ that
holds? The answer is yes, but we won't prove it in this post. In fact there are
multitude of ways of proving a valid $n \leq m$. Just as an example, we'll give
another proof of `oneLEQtwo`.

```haskell
oneLEQtwo' :: 'S 'Z <= 'S ('S 'Z)
oneLEQtwo' = Double $ Single $ Base
```

You might have noticed that, the order at which we apply `Double` and `Single`
does not matter. So to produce a valid $n \leq m$, we can start with `Base` that
is $0 \leq 0$, we need to apply $m - n$ `Single`s and $n$ `Double`s in any order
to produce $n \leq m$.

### Singletons: faking dependent types

We can use the algorithm for reaching to any valid $n \leq m$ to recover $n$ and
$m$ out of a given inequality. What would be the type of a function doing that?
We could try the following.

```haskell
recoverAttempt :: n <= m -> (n,m)
recoverAttempt = undefined
```

This doesn't work because $n$ and $m$ have kind `Nat` but we need them to be
`Type`s if we are going to produce a term at the value level. That is we need
dependent typing.

Sadly, Haskell is not there yet, so we need to fake it using _singletons_. The
idea is to create an indexed data type (via GADTs), so that there is exactly one
term for each indexing type. That is all a bit vague, let's just do it for
natural numbers.

```haskell
data SNat :: Nat -> Type where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)
```

You see while the type `'Z` has kind `Nat`, the type `SNat 'Z` has kind `Type`
and it has exactly one inhabitant that is `SZ`. This is true for all types of
kind `Nat`. Hence, we can use the singleton type `SNat n :: Type` as the
term-level representatives of `n :: Nat`.

Now, we can write the recovery function.

```haskell
recover :: n <= m -> (SNat n, SNat m)
recover Base = (SZ, SZ)
recover (Single nLEQsm) | (x,y) <- recover nLEQsm = (   x, SS y)
recover (Double nLEQm)  | (x,y) <- recover nLEQm  = (SS x, SS y)
```

We are already using the inductive structure of `n <= m`. The `Single`
constructor increments the right side of `<=` and `Double` increments both
sides, so we turn these constructors on explicit increments to recover the
singletons corresponding to `n` and `m`.

## Rank encoded leftist heaps

We have everything needed to encode the leftist property of a leftist heap into
data type. Since the leftist property relates the ranks of subheaps and the
current heap, we first create `Rank` data type that encodes the rank using a
type-level `Nat`. We also define a helper to increment the rank for later use.

```haskell
newtype Rank n = Rank { _unRank :: SNat n }

inc :: Rank rank -> Rank ('S rank)
inc (Rank snat) = Rank (SS snat)
```

Since the heaps will be indexed by the heap rank, we need to use GADTs again.

```haskell
data SafeHeap :: Nat -> Type -> Type where
  Leaf' :: SafeHeap 'Z a
  Node' :: a -> Rank ('S m)             -- Node' data
        -> SafeHeap n a -> SafeHeap m a -- Children
        -> m <= n                       -- Leftist invariant
        -> SafeHeap ('S m) a
```

After all this work, the data type declaration does not look so bad. The `Leaf'`
constructor creates a `SafeHeap` of rank 0. The `Node'` constructor grows the
heap only when we can show that the rank of the right subheap is less than or
equal to that of the left subheap. Further, the resulting heap has rank one more
than that of the right subheap.

What did we just do? We created a data type whose inhabitants are either vacuous
(infinite loop, `undefined`, etc.) or that it is a tree satisfying the leftist
property. Let's try some examples.

```haskell
heap1 :: SafeHeap ('S 'Z) Int
heap1 = Leaf'
```

This fails because the `Leaf'` constructor forces the rank to be `'Z` instead of
`'S 'Z` as given in the type signature.

```haskell
heap2 :: SafeHeap ('S 'Z) Int
heap2 = Node' 42 ('SS 'SZ) Leaf' Leaf' Base
```

This type checks because `Leaf'`s have rank `'Z` and `Base` proves `'Z <= 'Z`.

```haskell
heap3 :: SafeHeap ('S 'Z) Int
heap3 = Node' 42 ('SS 'SZ) heap2' Leaf' (Single Base)
```

This also type checks because the right child still has a lower rank (`'Z`) than
the left child (`'S 'Z`) and we can prove `'Z <= 'S 'Z` via `Single Base`.

```haskell
heap4 :: SafeHeap ('S 'Z) Int
heap4 = Node' 42 ('SS 'SZ) Leaf' heap2' ???
```

Unless we replace `???` with a fallacious term such as `undefined`, we won't be
able to find a proof for `'S 'Z <= 'Z`, hence whatever we put won't type check.
This is precisely how the data type prevents us from violating the leftist
property.

We just made terms that violate the leftist property illegal. Pretty cool, huh?

## Heap instance for SafeHeap

So most people who read up on type-level programming gets to the previous stage
of making property violating terms illegal. The next step is to operate on the
data structure, which is where things get complicated. Say that we tried to make
`SafeHeap rank a` an instance of `Heap`.

```haskell
instance Ord a => Heap (SafeHeap rank a) where
  type Elem (SafeHeap rank a) = a
```

We're already in a bad place. This forces the type of `merge` to be `SafeHeap
rank a -> SafeHeap rank a -> SafeHeap rank a`. This is not at all what we want.
We want to be able to merge heaps of different ranks as we did in the untyped
implementation. Further, this signature requires us to produce a heap of rank
identical to the input heaps. This is clearly not going to fly.

Let's say that we gave up on the type class and decided to define all the
operations at the top-level. Then we could give `merge` the type `SafeHeap rank1
a -> SafeHeap rank2 a -> SafeHeap (Fx rank1 rank2) a`. Here `Fx` is some type
level function on `rank1` and `rank2`. This allows inputting heaps of different
ranks, but we still need to figure out the rank of the output. This signature
presupposes that to be a function of `rank1` and `rank2`, but in fact it
_depends_ on the whole input heaps. The word "depend" should raise a red flag.
Do we need to create singletons for `SafeHeap`s as well now? Normally, you get
to this question and give up on the whole approach and revert back to vanilla
types (at least I used to). Clearly, this line of thinking is not productive.

The question we should be asking is what was our original goal? It was to
preserve the leftist property. Does that really require establishing the effect
of operations on the rank of the heap at type level? No, not really. If we are
talking about the `merge` operation what we want is to input two `SafeHeap`s of
whatever rank and produce some `SafeHeap` of whatever rank. The fact that the
output is `SafeHeap` is enough to ensure the leftist property is preserved,
which is our goal.

The way to do that is to hide the rank. This can be done using the
`ExistentialQuantification` extension which gives us existential types. Let's do
that for `SafeHeap`.

```haskell
data SomeSafeHeap label = forall rank. SSH (SafeHeap rank label)
```

Although it uses the keyword `forall` what we really mean is "within
`SomeSafeHeap a` there exists a `rank` such that `SafeHeap rank a`". Hence, the
name existential types. So the type instance we are after is the following:

```haskell
instance Ord label => Heap (SomeSafeHeap label) where
  type Elem (SomeSafeHeap label) = label
```

The type of `merge` now is `SomeSafeHeap a -> SomeSafeHeap a -> SomeSafeHeap a`
which makes no assertion about the ranks of the input or the output, yet
everything involved is a leftist heap. This is exactly what we want.

**The key take away:** if you use fancy types, reach for the existential as soon
as possible.

This is not to say that you shouldn't try to implement operations that requires
relating ranks of inputs and outputs. If it is straightforward, it will give you
more guarantees, which is yey! The question is whether it is worth it.

The `singleton` function for `SomeSafeHeap a` is a trivial example of this. We
know that the singleton heap should have rank 1 at compile time. Since rank
information is hidden behind an existential, there is nothing preventing us from
defining `singleton x` to be `empty`, which type checks fine. However, if we
extract the `SafeHeap ('S 'Z) a` into its own definition, we can reduce the
likelihood of such a mistake.

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
unwrapping and wrapping with `SSH`. This makes sense because as we pointed in
the unverified version, `mkNode` is where the leftist property is preserved by
placing the heap with the smaller rank to the right.

### Comparing without forgetting

We used to do it using the term-level `(<=)` operator on the rank which was an
`Int`. So it seems all we need is to provide an analogous operator for `SNat`s.
However, this omits the fact that we also need the proof that the rank of the
right child is less than the rank of the left child and a `compare` or `(<=)`
like operator despite determening that at term-level forgets about it
immediately returning an `Ordering` or a `Bool` only.

What we want here is _connexity_, that is given any $n$ and $m$, either $n \leq
m$ or $m \leq n$. This is the case as $\leq$ on natural numbers is a [total
order](https://en.wikipedia.org/wiki/Total_order). It is also the case that this
property is very natural to express as a function.

```haskell
lemConnexity :: SNat n -> SNat m -> Either (n <= m) (m <= n)
lemConnexity SZ y = Left  (lemZLEQAll y)
lemConnexity x SZ = Right (lemZLEQAll x)
```

The base cases are simple, we need to show $0 \leq m$ and $0 \leq n$. Since $0
\leq x$ holds for all $x$, we can prove a lemma to handle both. We imagine for
the moment that `lemZLEQAll :: SNat n -> Z' <= n` exists. This make-believe with
lemmas is basically how top-down proofs work. As you focus on the proof at hand,
you postulate reasonable looking statements.

The inductive case is equally simple and gives a good opportunity to introduce
_typed holes_.

```haskell
lemConnexity (SS x) (SS y) = _
```

So the way you work with GADTs is that you pattern match and see what you got.
At this point the type for the type hole `_` is `Either ('S n1 <= 'S n2) ('S n2
<= 'S n1)` where `x` is `'SNat n2` and `y` is `SNat n1`. So we can recursively
call `lemConnexity` to obtain a proof of `Either (n1 <= n2) (n2 <= n1)` and
pattern match.

```haskell
lemConnexity (SS x) (SS y) =
 case lemConnexity x y of
   Left  xLEQy -> _
   Right yLEQx -> _
```

Now we have two typed holes. We are trying to get to `Either ('S n1 <= 'S n2)
('S n2 <= 'S n1)` from `xLEQy :: n1 <= n2` and `yLEQX :: n2 <= n1` respectively.
The `Double` constructor produces a new inequality from a valid inequality by
incrementing both sides. Combined with `Left` or `Right` depending on the case,
we can provide a term for the desired type in both cases.

```haskell
lemConnexity (SS x) (SS y) =
 case lemConnexity x y of
   Left  xLEQy -> Left  (Double xLEQy)
   Right yLEQx -> Right (Double yLEQx)
```

We are now almost done with `lemConnexity`. Earlier we postulated `lemZLEQAll`
for the base cases, we still need to prove that. That is proven by induction
over the natural numbers.

```haskell
lemZLEQAll :: SNat n -> 'Z <= n
lemZLEQAll SZ     = Base
lemZLEQAll (SS x) = Single (lemZLEQAll x)
```

That's it. We have proved some facts about natural numbers. It does not feel so
bad, mostly, it's just induction and looking at typed holes. The ergonomics of
doing that compared to Agda, Idris, or any other proof asistant is really
lacking. When we leave a hole, the output is cluttered, it is not easy to see
what is available in the context which is usually how you figure out how to
prove things. So beyond these basic facts life can be challenging, but I feel
for most data structures, you can get good mileage out of basic facts. If
anything Haskell forces you to make your lemmas as granular as possible.

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
construct a `Node'`.

# Verifying the heap property

Let's do it one last time, but this time with both the heap and the leftist
property.

So what is the heap property mathematically? For a node $n$ and its children $l$
and $r$, we have $\mathit{label}(l) \leq \mathit{label}(n)$ and
$\mathit{label}(r) \leq \mathit{label}(n)$.

You can immediately see that in addition to having the rank available at the
type level, we now also need the label. So far we allowed labels to be of an
arbitrary `Type`. To simplify the situation, we now decree that the labels are
based off of `SNat`s, allowing us to build on the existing theory of natural
numbers.

## Rank and label encoded leftist heaps

To avoid confusion we wrap the label `SNat`.

```haskell
newtype Label n = Label { _unLabel :: SNat n }
```

All the machinery needed to create a data type that makes heap property
violating terms illegal is already built. So here is the data type.

```haskell
data SaferHeap :: Nat -> Nat -> Type where
  Leaf'' :: SaferHeap 'Z 'Z
  Node'' :: Label a -> Rank ('S m)         -- Node' data
         -> SaferHeap n b -> SaferHeap m c -- Children
         -> m <= n                         -- Leftist property
         -> b <= a -> c <= a               -- Heap property
         -> SaferHeap ('S m) a
```

`SaferHeap` looks a lot like `SafeHeap`, except for the fancy-typed label and
two more inequalities to ensure the heap property is satisfied in `Node''`.

`Leaf''` carries a type-level label of `'Z` now. Every `SaferHeap` needs a
type-level label to form the type. Using `'Z` is a nice work around because it
is the least natural number, hence it doesn't inhibit construction of a `Node''`
with any label.

There are two immediate alternatives to this:

 1. Use `Maybe Nat` rather than `Nat` for the `SafeHeap` label, but that
 requires us to change the heap property to so that rather than requiring `b <=
 a`, we require "given `b` is `'Just b'`, `b' <= a`" and similarly for `c <= a`.

 2. Use `Maybe Nat` again, but instead of changing the heap property in
 `Node''`, we have three `Node''` like constructors: one with both children
 having `'Just` labels, one with only the left child having a `'Just` label, and
 one with neither having `'Just` labels (why don't we need the fourth case?).
 This way the heap property remains as simple inequalities.

In a way, (1) and (2) are equivalent solutions. One might say they are cleaner
than exploiting `'Z` being the least element in a total order. Both, however,
especially (2) complicates every function that needs to scrutinise a
`SaferHeap`.

The next step is to wrap the wrap the data type in an existential like the last
time.

```haskell
data SomeSaferHeap = forall rank label. SSH' (SaferHeap rank label)
```

At this point, you might like to construct some `SaferHeap`s to see the
ergonomics of constructing this type by hand as well as get the satisfaction of
type errors due to heap property violation. I think you'll agree that
constructing nested `Node''`s is tedious, but luckily we use the nice interface
`Heap` instead.

## Heap instance for SaferHeap

Just as before the instance is for the existentially wrapped type.

```
instance Heap SomeSaferHeap where
  type Elem SomeSaferHeap = Nat
```

The `Elem` instance for `SomeSaferHeap` is interesting because, we don't
actually store `Nat`s anywhere in the nodes, we only store `SNat`s. Then
`insert` will require conversion from `SNat` to `Nat` and `findMax` from `Nat`
to `SNat`. The `SNat` to `Nat` direction is easy.

```haskell
demote :: SNat n -> Nat
demote SZ     = Z
demote (SS n) = S (demote n)
```

But the opposite direction would have a signature `Nat -> SNat n`. Let's try to
write that.

```haskell
promoteAttempt :: Nat -> SNat n
promoteAttempt Z                                = SZ
promoteAttempt (S n) | snat <- promoteAttempt n = SS snat
```

Well, this does not type check, because one branch returns `SNat 'Z` and the
other `SNat ('S m)` for some `m`. Neither `'Z` nor `'S` unifies with the free
variable `n`.

Since our heap operations are on existentially wrapped types, we know that we
only need the promoted type-level `n` during the course of a function definition
only. So we do not really care what `n` is going to be so long as there is
_some_ n that we can embed in the heap. This smells like an existential. So the
`promote` should return an existentially wrapped `Nat`.

```haskell
data SomeNat = forall n. SomeNat (SNat n)

promote :: Nat -> SomeNat
promote Z                                 = SomeNat SZ
promote (S n) | SomeNat snat <- promote n = SomeNat $ SS snat
```

A good exercise at this point is to try to implement `singleton` for
`SomeSaferHeap`. It is very similar to the implementation for `SomeSafeHeap`
except you need to use `promote` and provide evidence for the heap property. The
answer is in [the full source code](#full-program).

## Merging safer heaps

The merge operation is, once again, all we care about. The overall structure is
going to be the same, but we'll need more plumming and lemmas.

### Making nodes

This time let's start from `mkNode`. Here's an attempt analogous to the previous
`mkNode`.

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

This attempt fails because we do not have the necessary inequalities to provide
evidence for the heap property. We do have access to the parent label and and
the children labels, so we could decide on whether they hold. But this approach
would require us to give the signature to `mkNode` because we need to handle the
case `vc` is smaller than one of the labels of the children. Besides, this
information is already computed if we follow the structure of the previous merge
implementation. So let's assume that the necessary inequalities are passed down
by `merge`.

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

This doesn't work either because we have an `a <= c` for the first
`SomeSaferHeap`, but that type hides `a`, so as far as the type-checker is
concerned the rank of `hA` has nothing to do with `Rank a`.

It looks like we're hiding too much. Since `mkNode` is not part of the `Heap`
typeclass, perhaps we can use `SaferHeap` instead of `SomeSaferHeap` in the
signature of `mkNode`. Then one possible signature for `mkNode` would be the
following.

```haskell
mkNode :: Label c
       -> SaferHeap r1 a -> SaferHeap r2 b
       -> a <= c -> b <= c
       -> SaferHeap ??? c
```

This type signature relates the type-level labels of the heaps to the
inequalities, but it also requires handling ranks. There are three viable
choices for `???`: `r3`, `'S r1`, and `'S r2`. The first one runs into the same
problem as `promote`, the calculated node rank won't unify with the free type
variable `r3`. The last two can be made the work but it presupposes that the
caller already knows which heap is going to be the right child, hence `mkNode`
would be pointless.

It looks like `SomeSaferHeap` hides too much and `SaferHeap` reveals too much.
What we need is something in the middle. We want to hide the rank, but leave the
type-level value visible. Once again existential types come to the rescue.

```haskell
data AlmostSomeSaferHeap label = forall rank. ASSH (SaferHeap rank label)
```

We can now proceed to write a `mkNode` that looks a lot like the implementation
for `SomeSafeHeap`.

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

We can tackle `merge` now. At the top-level interface we're using
`SomeSaferHeap`, but the actualy merge is going to happen in
`AlmostSomeSaferHeap`. The reason for that will become clear later.

```haskell
merge (SSH' h1) (SSH' h2) | ASSH mergedHeap <- merge' (ASSH h1) (ASSH h2) =
  SSH' mergedHeap
```

Then the signature and the base cases of `merge'` are as follows

```haskell
merge' :: AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
       -> AlmostSomeSaferHeap (Max a b)
merge' (ASSH Leaf'') heap = heap
merge' heap (ASSH Leaf'') = heap
```

This brings me to the penultimate corner stone of type-level programming in
Haskell that I'll cover in this post: type-level functions. We have already used
associated type families within the `Heap` and `HasRank` type classes which are
technically type-level functions, but they are too trivial. `Max` on the other
hand does recursion and everything!

#### Type families

The type-level `Max` function is defined using a closed type family enabled by
the `TypeFamilies` extension.

```haskell
type family Max (n :: Nat) (m :: Nat) :: Nat where
  Max 'Z m          = m
  Max n 'Z          = n
  Max ('S n) ('S m) = 'S (Max n m)
```

This is analogous to the following term level `max` function on `Nat`s.

```haskell
max :: Nat -> Nat -> Nat
max Z m = m
max n Z = n
max (S n) (S m) = S (max n m)
```

You might be wondering why not just write that and get a promoted version of
`max` just as we did with data types and kinds? It's an excellent question and
this syntactic dicothomy is another reason why people don't like type-level
programming in Haskell. In Idris or Agda, that is exactly how it works.

This problem stems from multiple reasons. For one thing type families existed in
GHC since 2007, whereas data type promotion was added in 2012, and the mandate
for moving term and type levels closer is fairly recent. Further, adding type
level computation into Haskell is an after-thought, so you need to retrofit
the syntax. On top of that the behaviour of type families is different than
functions, the patterns of a type family can do unification whereas pattern
matches of a function can't.

For example, the following returns the type `Int` if its arguments unify and
`Char` otherwise.

```haskell
type family Same a b where
  Same a a = Int
  Same _ _ = Char

sameInt :: Same [ a ] [ a ]
sameInt = 42

sameChar :: Same (Maybe a) [ a ]
sameChar = 'c'
```

So although we can promote term-level functions to the type-level (`singletons`
library allows this via Template Haskell), they are still not equivalent in
behaviour because term-level variables act differently compared to type-level
variables.

As a result using the same syntax for both would not be possible in general as
we'd need unification at the term level as well.

#### Type families vs GADTs

We could have encoded `Max` as a GADT as well and similarly we could have
encoded `<=` as a type family.

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
we would have used different lemmas, but they would have worked. However, there
are still reasons to choose one encoding over the other.

 1. If you intend to do induction over your relation, then constructors are
 helpful, so GADTs get a point.

 2. If what you have is a function, then the GADT encoding forces you to add
 another type variable for the result and the functional dependency between the
 result and the arguments get lost.

 3. Conversely, if you have a relation that is not a function and you choose to
 use a type family, since there is no clear result variable, you need to return
 a type of kind `Bool` or something equivalent.

 4. With type families when you learn more information about the type, the
 reduction happens automatically, whereas with GADTs you need to modify and pass
 the relation around.

 5. More practically, you might already have some type level relations/functions
 in your codebase and you might want to stay consistent with semantically
 related relations. Beyond consistency, this might allow you to reuse some
 lemmas via duality or generalisation.

My choices in this post embody the first three principles. Also, I wanted to
show one of each.

#### Getting back to the merge

We can now understand why the base case type checked at all.

```haskell
merge' :: AlmostSomeSaferHeap a -> AlmostSomeSaferHeap b
       -> AlmostSomeSaferHeap (Max a b)
merge' (ASSH Leaf'') heap = heap
merge' heap (ASSH Leaf'') = heap
```

In the first base case, we have `Max 0 b` which is `b` by definition and `b` is
exactly the value of `heap`. It works similarly for the other base case.

In the previous version, we needed the term-level `(<=)` to see which label to
keep on top and which spine to recurse on. We have already seen while verifying
the leftist property that `lemConnexity` is the replacement we need for
comparing `SNat`s. By following the unverified implementation, we can provide a
partial implementation that doesn't type check.

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

Let's focus on the `Left` branch first. The type checker at this point complains
about the holes, but more importantly it complains about the terms involving
applications of `mkNode` even with the assumption that `c1LEQp` and `c2LEQp`
have appropriate types. The exact complaint is "`Could not deduce: Max a b ~
b`". Here `~` means types are equal.

But of course! We have `aLEQb` of type `a <= b`, but the type checker is too
stupid to know that this implies `Max a b` is just `b`. So we need to prove
this. That brings us to _propositional equality_.

#### Propositional equality

The following is arguably the data type that took me longest to get my head
around. So if you have trouble with it, just keep using it until it clicks.

```haskell
data (:~:) :: k -> k -> Type where -- Same as that in Data.Type.Equality
  Refl :: a :~: a
```

This `(:~:)` takes two types of the same kind and is poly-kinded. When you think
about it, it has to be. If it was restricted to `Type` or `Nat` that would make
it a type equality suitable only for proving two `Type`s equal or two `Nat`s
equal. This version makes no assumptions.

This type allows us to prove two types in Haskell are equal and can be replace
with one another. The idea is if you have a term with type `a :~: b` and you
pattern match on it, the only case is the `Refl` constructor.  Just like
previous pattern matches on GADTs, this refines the type in context. In this
case, it reveals that `a` and `b` are one and the same, that is the type checker
learns `a ~ b`.

We need `Max n m ~ m` given `n <= m`. So we are trying to show `Max n m :~: m`.
We can do this by induction on `n <= m`.

```haskell
lemMaxOfLEQ :: n <= m -> Max n m :~: m
lemMaxOfLEQ Base = Refl
```

In the base case, we pattern match on `Base` which reveals both `n` and `m` to
be 'Z. So we need to show `'Z :~: 'Z`. Since `Refl` has type `a :~: a`, we can
trivially instantiate `a` to `'Z` to get the desired equality.

Then comes the first inductive case with `Double` constructor.

```haskell
lemMaxOfLEQ (Double xLEQy) | Refl  <- lemMaxOfLEQ xLEQy = Refl
```

Here, `xLEQy` has type `n <= m` and we need to show `Max ('S n) ('S m) :~: 'S
m`.  By definition of `Max`, the type checker already reduces the goal to `'S
(Max n m) :~: 'S m`. Since, `xLEQy` is smaller than the original argument, we
can recursively call `lemMaxOfLEQ` to get a term of type `Max n m :~: m`.
Pattern matching on that tells the compiler `Max n m ~ m`, so the overall goal
reduces to `m ~ m`. Once again `Refl` constructor trivially proves this. The
process as you can see is fairly mechanical.

The final inductive case is only a tiny bit more complicated, but still
managable.

```haskell
lemMaxOfLEQ (Single xLEQy) =
  case fst $ recover xLEQy of
    SZ                                           -> Refl
    SS _ | Refl <- lemMaxOfLEQ (lemDecLEQ xLEQy) -> Refl
```

The term `xLEQy` has type `n <= m` and we need to prove `Max n ('S m) :~: 'S m`.
Since we don't know if `n` is built with `'S` constructor (it could be `'Z`), we
don't get an automatic reduction of our goal like last time. We still have
`xLEQy`, so we could apply `lemMaxOfLEQ` recursively. That would get us `Max n m
:~: m`, but pattern matching on that doesn't get us to `Max n ('S m) :~: 'S m`.

The mechanical process got stuck. It's time to take a step back and think.
Taking inspiration from the previous case, if we knew that `n` was of the form
`'S k`, our goal would reduce to `'S (Max k m) :~: 'S m`. Then we could show
`Mak k m :~: m` and that would reduce the overall goal to a trivial proof
obligation. To obtain `Max k m :~: m`, we need a recursive call to `lemMaxOfLEQ`
with `k <= m`, but we only have `'S k <= m`. Our grade school maths intuition
tells us $k + 1 \leq m \implies k \leq m$. So all we need is a lemma. In our
implementation that is `lemDecLEQ` of type `'S n <= m -> n <= m`.

But we forgot something! This all hinges on `n` being of the form `'S k`, what
if it isn't?  Well, the only other thing it could be is `'Z`, but then `Max 'Z m
:~: m` trivially reduces to `m :~: m`, so we are good.

Alright, we can prove our final lemma. I'm only showing this one because it will
allow me to complain about Haskell.

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

There is nothing particularly difficult about this lemma apart from doing
induction on (<=) and its constituents together. It is not particularly
difficult given all we have seen so far. But it does contain some lessons.

Haskell doesn't have a termination checker. This is a feature, but it sure feels
like walking barefoot after you break a glass when you are trying to prove
things. You could accidentally create an infinite loop that type checks but
does not constitute a valid proof. This lemma's proof is particularly
vulnerable because we are pattern matching on three different variables which
makes it easy to construct an infinite loop.

We remedy this in `lemDecLEQ` by making the recursive calls in the body of `go`
to `lemDecLEQ` rather than `go` itself. This is less efficient but it makes it
easy to see that each recursive call is to something strictly smaller than what
we started with.

The other interested bit is the base case of `go`.

```haskell
go :: SNat ('S n) -> SNat m -> 'S n <= m -> n <= m
go _ SZ _ = error "Inaccessible case."
```

The reason we use `error` is not because there is an error but because of a
syntactic deficiency of `Haskell`. If the second argument is `SZ`, then there
are no constructors of `(<=)` that can make `'S n <= m` which we have a proof
for, namely the third argument. We can see this easily by pattern matching on
  the third argument.

```haskell
go :: SNat ('S n) -> SNat m -> 'S n <= m -> n <= m
go _ SZ Base     = undefined
go _ SZ Single{} = undefined
go _ SZ Double{} = undefined
```

If you compile this, GHC will give you pattern match inaccessible warnings
combined with type errors about why these arguments can't coexist together. It
can't be a problem with our output because undefined can take any desired type.

In languages like Agda and Idris, you'd make this an inaccessible case. For
example, in `Idris` it looks like the following.

```haskell
go _ SZ _ impossible
```

Then the compiler can confirm or deny that is the case. Since we don't have this
snytax in Haskell (there was a
[proposal](https://gitlab.haskell.org/ghc/ghc/issues/10756#comment:4)). What if
we omit this case altogether? The problem with that is because in an omitted
case we don't pattern match on the second argument, GHC doesn't know that the
pattern is inaccessible, hence it reports a non-exhaustive pattern match
warning.

This is very dangerous if you are theorem proving because you might prove a
lemma, then tweak it slightly and not realise that the inaccessible case is now
perfectly accessible. Because we have `error "Inaccessible case"` in the body of
that case, it type checks just fine making the proof incomplete at best, wrong
at worst (if there was no way of handling that particular case). We get no
warnings about it either.

How about the rest of the process, is explaining facts to the type checker also
Haskell's fault? Yes and no.

Fundamentally, it's the grand challange of interactive theorem proving to elide
tedious details, so we can work on the big insights. We are not there yet. There
is a lot of [ongoing
research](https://www.cl.cam.ac.uk/~lp15/Grants/Alexandria/) especially focusing
on combining machine learning techniques with proof search to automatically find
little facts that would make the process more smooth. However, you need to
recognise that this is a very general program synthesis problem which is
undecidable in general and very difficult even in particular cases.

That said, Haskell lacks the most basic facilities to this end. For example,
basic proof search in Agda and Idris would allow you to automatically fill in
the proof of basic propositions and even accepts hints (lemma names to use) to
do some rudimentary search. It allows you to leave some terms implicit and tries
to fill in the details on its own. The closes Haskell has is valid type holes,
which are suggestions to fill typed holes in the error messages. The ability
to interact with the compiler by pattern matching and typed hole refinements
is also mostly missing (with the exception of `ghc-mod` without reliable
editor support).

#### Getting back to the merge again

Focusing on the `Left` branch only, we make it known to the compiler that `a
<= b` implies `Max a b ~ b` using `lemMaxOfLEQ` that we have just proved.

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
```

This definition still doesn't type check because we have holes, but we no longer
have a type error because of `mkNode` function application.

At this point, what we want to do is to inspect the error messages for the typed
holes to see what the types the terms we need to construct have. Well, according
to GHC they both need type `t` (distinct rigid `t`s). Incredibly unhelpful.
Honestly, I don't know what's going on there. However, if you inline the `let`
binding, we get better results.

```haskell
mkNode vB (ASSH bLeft) (merge' (ASSH bRight) (ASSH hA)) _ _
```

The first hole needs a type `l <= b` and that's exactly the type of `lLEQb`. The
second hole needs `Max r a <= b`, we do not yet have a term corresponding to
this type, but we have `rLEQb :: r <= b` and `aLEQb :: a <= b`. `Max` is a
selective function, and it doesn't matter which choice it makes, we got it
covered. We just need a lemma to prove that. The types for the required lemma
and the selectivity lemma needed to prove that are as follows.

```haskell
lemDoubleLEQMax :: n <= l -> m <= l -> Max n m <= l
lemMaxSelective :: SNat n -> SNat m -> Either (Max n m :~: n) (Max n m :~: m)
```

I won't prove these. I think you are in a great position to do it yourself at
this point. If you get stuck, the proofs are at the end of the post.

We can now give the full definition of the `Left` branch.

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
not required in the `Left` branch because of the ways we set things up. If you
write the `Right` as we did `Left`, the type error should give you a clue what
lemma is needed. If you can't figure it out that too is at the end of the post.

#### Other operations?

We are done! No more verification. We could implement the other methods but just
as in the previous implementation, there is nothing interesting there.

# Simulating heap operations

So after going through all this trouble to prove properties of our code, why
bother testing? The answer is multifaceted.

 1. We didn't verify everything. Earlier we gave the example that we could
 satisfy type of the `singleton` function by discarding its argument and placing
 empty. Another common theme is to discard a subpart of the data structure and
 accidentally use the other part twice. In the case of heap property, if one
 subtree satisfies the heap property, we could use it in the other branch as
 well and the proof would go throug even though we discarded elements. If we had
 linear types, we could have guarded ourselves against this.

 2. Haskell's proof system is unsound due to non-termination, `Type : Type`, and
 other reasons. We might have a fallacious proof somewhere that makes it look
 like a property is verified to the type checker while being incorrect.

 3. It gives me a chance to talk about another type-level computation feature:
 visible type applications.

 4. I really want to use QuickCheck to run simulations on the heap. It's super
 neat. I won't lie, this might be the reason why this section exists.

## Generating actions

We're only going to simulate insertion and deleting the min. Here's the initial
encoding of the actions.

```haskell
data Action a = Insert a | DeleteMax deriving Show
```

Let's give `Arbitrary` instances for `Nat` and `Action`, so that we can randomly
generate them.

```haskell
instance Arbitrary Nat where
  arbitrary = fromInt . getPositive <$> arbitrary @(Positive Int)
    where
    fromInt 0 = Z
    fromInt n = S (fromInt (n - 1))

instance Arbitrary a => Arbitrary (Action a) where
  arbitrary = do
    n <- arbitrary @Int
    if n `mod` 2 == 0
      then Insert <$> arbitrary
      else pure DeleteMax
```

Somewhat arbitrarily we choose between a deletion and an insertion with $50%$
probability. This may or may not be a realistic simulation, but it is something
easy to adjust. You could have multiple wrappers over `Action a` such as
`DeleteHeavy a` and `InsertionHeavy a` so that you can simulate different
scenarios, but we don't bother with it today.

There is one type-level computation related feature in these instances that we
haven't discussed yet. That is the `TypeApplications` extension.

### There is $\Lambda$ then there is $\lambda$

If someone asks for the explicitly typed lambda term for the polymorphic
identity function (as they do), we'd probably write $\lambda x : \alpha. x$,
where $\alpha$ is a polymorphic type variable. We'd expect this function to be a
closed term that is to say it should be independent of the context. That term
looks like it is independent of the term-level variables, but $\alpha$ looks
like it is very much depends on whatever $\alpha$ is in the context. That is
because there is nothing binding $\alpha$.

Luckily, in Haskell this is not true although we write the equivalent of the
term above syntactically (or even less thanks to type inference), what Haskell
interprets that as is $\Lambda \alpha : \mathit{Type}. \lambda x : \alpha. x$.
The syntax for this in Haskell is the following. Although you can't write a term
like this in Haskell, you can explicitly put $\alpha$ in the type signature with
`ExplicitForAll` extension.

```haskell
id :: forall a. a -> a
id x = x
```

The `forall a` corresponds to $\Lambda \alpha$, where the kind `Type` is
inferred.

If we have type level functions with explicit type variables, then why do we
never see type level applications? Well, it happens all the time, it is just
behind the scenes. When you apply `id` to 42, the first thing that happens is
that `Int` gets passed to the the type-level function. GHC relatively recently
intorduced `TypeApplications`, which gives a syntax to do this explicitly. You
just pass the type with a `@` prefix. For example in `ghci`, we can query `:t
id @Int` and we get `Int -> Int`.

This works as an alternative to using `::` when the type is ambiguous. Often it
lets us get away with fewer parantheses and looks cleaner in general.

What happens if there are multiple type variables? Well, the type application
unifies the type with the first type-variable which is how term-level
application works as well.

The problem is if we don't use `ExplicitForAll` the ordering of type variables
is determined implcitly. You can use `:type +v` to query the order of type
variables used by GHC. I suggest you explicitly put `forall`s when it matters if
you're going to use type applications.

The type applications in the arbitrary instances are somewhat trivial uses of
it. We'll see something more exciting momentarily.

## Executing actions

We can now interpret the initial representation of the actions. Nothing exciting
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
implementing `Heap` and a series of actions, executing these actions on both in
order starting from each implementation's `empty` heaps should result in the
same maximum.

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

The actual computation is not very interesting, but the way we direct it is.
First, we use an explicit `forall`, you might think this is to fix the ordering
of heap implementations, but in this function it doesn't matter which order they
are in since both `heap` and `heap'` are passed to the same function. The reason
we enable it is so that we can use `ScopedTypeVariables` extension which allows
us to refer to the type variables in the signature within the body of the
function.

The type applications `@heap` and `@heap'` determine the computation.  This is
not just disambiguation. If both `maxOfActions` were applied to `heap` instead,
we'd create a property that is trivially satisfied since we apply the actions to
the same implementation and not do anything with `heap'`.

Then we use a type application again in the body of `maxOfActions`. Without it,
the list of actions would only give `Elem h` which in our case will be `Nat` or
`Int`, but this says nothing about which implementation of `heap` to do (another
way of phrasing this is the `Elem` type family is not injective, so we can't go
back from `Elem h` to `h`). Hence, we use a type application again to clarify
which implementation `carryOutActions` should use.

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
the reference implementation and the untyped leftist heaped, leftist property
verified leftist heap, and the leftist and heap property verified leftist heap
in that order.

Then I just sample some actions and see the result of carrying them out on the
terminal because I'm paranoid like that (the `Arbitrary` instance could also be
buggy =)).

At this point, we can be reasonable sure that these implementations are correct
(at least for insertion and deletion and probably for merge).

# Conclusion

After such a long post, I'll keep the conclusion short and sweet. Here's what we
did in a gist:

 - learnt about leftist heaps a purely functional replacement to array-based
   binary heaps;
 - looked at all major parts of Haskell's type-level computation features;
 - ran simulations to test functional equivalence of various implementations;
 - gave a commentary of Haskell as an interactive theorem prover.

What is the overall verdict on that last point? It's not ideal at all, but it
works at least for simple data structures and properties. If we had used the
`singletons` library and type checker plugins, we could have gone farther and
get there quicker. I think the point that is overlooked in these discussions is
that GHC provides the means for doing verification natively and also produces
highly optimised code and has a huge ecosystem. Neither Agda nor Idris nor ATS
can claim this. I for one am looking forward to Haskell's journey in this
direction.

## Acknowledgements

This implementation wouldn't be possible without the heroic work by [Dr
Richard Eisenberg](https://richarde.dev/index.html) and [Prof. Stephanie
Weirich](https://www.cis.upenn.edu/~sweirich/) ([closed type
families](https://dl.acm.org/citation.cfm?id=2535856),
[singletons](https://dl.acm.org/citation.cfm?id=2364522)), [Dr James
Cheney](https://homepages.inf.ed.ac.uk/jcheney/), [Prof. Ralf
Hinze](https://www.cs.ox.ac.uk/ralf.hinze/), [Dr Hongwei
Xi](https://www.cs.bu.edu/~hwxi/) ([GADTs
1](https://ecommons.cornell.edu/handle/1813/5614) and [GADTs
2](https://dl.acm.org/citation.cfm?id=604150)), and many GHC implementors.  It
also wouldn't have been as slick if it wasn't for the wonderful presentations by
Prof. Weirich on [verifying red-black
trees](https://www.youtube.com/watch?v=n-b1PYbRUOY)
([alternative](https://www.youtube.com/watch?v=rhWMhTjQzsU)).

# Full program
