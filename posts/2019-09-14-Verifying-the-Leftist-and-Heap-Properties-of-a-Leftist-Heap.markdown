---
title: Verifying the Leftist and Heap Properties of a Leftist Heap
postType: Technical
inWhich: my job search leads me to verify the titular properties of a leftist
  heap using Haskell's type-level features and test it by way of simulation
  using QuickCheck. This post doesn't assume experience of type-level
  programming.
published: false
---

## The story

I've made it to the final stage of my computer science PhD, you know the one
where you start looking for jobs, get yourself a copy of [Cracking the Coding
Interview](https://amzn.to/2Q74ckU) (affiliate link), and realise that you
haven't done much of the kind of programming that about half of the companies
expect you to do at their job interviews (and at their job interviews only).

Some point in the book it says "know how to implement these data structures by
heart: dynamically sized arrays, hash tables, [...], **heaps**, [...]".  It
downed on me that I remember the heap property and its interface, but not how to
implement it. Then I looked at Wikipedia and was horrified to be reminded that
despite conceptually being a tree, heaps are predominantly implemented using
arrays. At that point that despite having used Haskell as my primary language,
decided to implement it in Ruby---my prior primary language. After some time and
indexing errors later, I got it working and having looked at it decided I can
port this easily to Haskell using the [`ST`
monad](http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Monad-ST.html).
After writing `STRef` one too many times, I got that working too, but it left
much to be desired. "Save the trees" yelled my terminal!

Then I consulted Dr Chris Okasaki's [Purely Functional Data
Structures](https://amzn.to/34ICTAM) (affiliate link). A leftist heap is one of
the first data structures discussed in the book. It has better asymptotic
complexity than the binary heap implementation, but is represented as a tree and
doesn't make use of mutation. Great. Having implemented that I was pleased to
have a heap under my belt that was much easier to remember and much more
difficult to get its implementation wrong.

Staring at it for a while (and being bored while trying to find various kind of
substrings in linear time and constant space), I got the burning desire to
encode the titular properties of a leftist heap using fancy types. Having
listened to hundreds of people (justifiably) complain about the state of
type-level programming in Haskell, I found the process to be pleasant enough
that I wanted to share it.

## The spiel

This brings us to the post at hand. The primary goal of this post is _not_ to
further my procrastination in your expense, but to show that verifying real
properties of data structures using dependent types in Haskell is not a
pipedream. Through the example of leftist heaps, we discuss verification in
Haskell in general. Point out its rough edges but also give some practical
advice to avoid pitfalls.

Since leftist heaps are not as common as binary heaps, I'll explain how they
work and how to derive the asymptotic complexities of its operations. So even if
you are not sold on the whole verification via fancy types in Haskell, you can
walk away from this post with a truly beautiful data structure.

Beginners beware! Type-level programming can be daunting. It certainly was for
me for a long time. I'll do my best to explain type-level computations from
scratch. If you find yourself getting confused, it's almost certainly my fault
and if you let me know, I'll update the post and do better.

## The itinerary

We start by looking at the heap interface and give a very simple and inefficient
implementation of it. Then we'll implement a leftist heap without fancy types
and explore how it works and why it's operations are asymptotically as efficient
as the array-based implementation. From there on, we step into the typed
territory. Instead of verifying the leftist and heap properties all at once,
we'll first implement a leftist heap with only the leftist property verified and
then another one with both the leftist and the heap properties verified. Along
the way we do some theory building for natural numbers from scratch. Finally, we
run simulations on various heap implementations using QuickCheck to have some
confidence that the the various implementations in this post are functionally
equivalent.

The exposition of the code won't be well-organised due to pedagogical reasons,
but I provide the full source at [the very end of the post](#full-program).
We'll use no libraries apart from
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

singleton x = Node x 0 Leaf Leaf

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

# Verifying the leftist property

# Verifying the heap property

# Simulating heap operations

# Conclusion

## Acknowledgements

This implementation wouldn't be possible without the heroic work by [Dr
Richard Eisenberg](https://richarde.dev/index.html) and [Prof. Stephanie
Weirich](https://www.cis.upenn.edu/~sweirich/) ([closed type
families](https://dl.acm.org/citation.cfm?id=2535856),
[singletons](https://dl.acm.org/citation.cfm?id=2364522)), [Dr James
Cheney](https://homepages.inf.ed.ac.uk/jcheney/), [Prof. Ralf
Hinze](https://www.cs.ox.ac.uk/ralf.hinze/), [Dr Hongwei
Xi](https://www.cs.bu.edu/~hwxi/)
([GADTs 1](https://ecommons.cornell.edu/handle/1813/5614) and
[GADTs 2](https://dl.acm.org/citation.cfm?id=604150)), and many GHC implementors.
It also wouldn't have been as slick if it wasn't for the wonderful presentations
by Prof. Weirich on [verifying red-black
trees](https://www.youtube.com/watch?v=n-b1PYbRUOY)
([alternative](https://www.youtube.com/watch?v=rhWMhTjQzsU)).

# Full program
