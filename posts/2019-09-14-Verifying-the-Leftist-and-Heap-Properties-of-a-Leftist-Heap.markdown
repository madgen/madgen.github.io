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
expect you to do at their job interviews.

Some point in the book it says "know how to implement these data structures by
heart: dynamically sized arrays, hash tables, [...], **heaps**, [...]".  It
downed on me that I remember the heap property and its interface, but not how to
implement it as I haven't done it in six years. Then I looked at Wikipedia and
was horrified to discover that something that is conceptually described as a
tree is predominantly implemented as an array. That was the point that despite
having used Haskell as my primary language, decided to implement it in Ruby---my
prior favourite language. After some time and indexing errors, I got it working
and having looked at it decided I can port this easily to Haskell using the `ST`
monad. After having written `STRef` one too many times, I got that working too,
but it left much to be desired, such inelegance, "save the trees" yelled my
terminal!

That was the point I consulted Chris Okasaki's [Purely Functional Data
Structures](https://amzn.to/34ICTAM) (affiliate link). One of the first data
structures discussed in the book. It has exactly the same asymptotic complexity
as the array-based implementation, but is represented as a tree and doesn't make
use of mutation.  Great. Having implemented that I was pleased to have a heap
under my belt that was much easier to remember conceptually and much more
difficult to get its implementation wrong.

Staring at it for a while (and having been bored by trying to find various kind
of substrings in linear time and constant space), I got the burning desire to
encode the titular properties of a leftist heap using fancy types. Having
listened to hundreds of people (justifiably) complain about the state of
type-level programming in Haskell, I found the end result to be so pleasant that
I wanted to share it.

## The spiel

This brings us to the post at hand. The primary goal of this post is not to
inflict my procrastination on you, but to show that verifying real properties of
data structures using dependent types in Haskell is neither very difficult nor
as inconvenient as people make it out to be. Along the post I'll try to share
some advice that applies to other data structures and their invariants and not
just to leftist heaps.

Beginners beware! Type-level programming can be daunting. It certainly was for
me for a long time. I'll do my best to explain type-level computations from
scratch. If you find yourself getting confused, it's almost certainly my fault
and if you let me know, I'll update the post and do better.

## The itinerary

We start by looking at the heap interface and give a very simple and inefficient
implementation of it.  Then we'll implement a leftist heap without fancy types
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
but I provide the full source at [the very end of the post](#Full-program).
We'll use no libraries apart from
[QuickCheck](http://hackage.haskell.org/package/QuickCheck-2.13.2).

## Acknowledgements

This implementation would not have been possible by the heroic work by [Dr
Richard Eisenberg](https://richarde.dev/index.html) and [Prof. Stephanie
Weirich](https://www.cis.upenn.edu/~sweirich/) ([closed type
families](https://dl.acm.org/citation.cfm?id=2535856),
[singletons](https://dl.acm.org/citation.cfm?id=2364522)), [Dr James
Cheney](https://homepages.inf.ed.ac.uk/jcheney/), [Prof. Ralf
Hinze](https://www.cs.ox.ac.uk/ralf.hinze/), [Dr Hongwei
Xi](https://www.cs.bu.edu/~hwxi/)
([GADTs](https://ecommons.cornell.edu/handle/1813/5614) and
[also](https://dl.acm.org/citation.cfm?id=604150)), and many GHC implementors.
It also wouldn't have been as slick if it wasn't for the wonderful presentations
by Prof. Weirich on [verifying red-black
trees](https://www.youtube.com/watch?v=n-b1PYbRUOY)
([alternative](https://www.youtube.com/watch?v=rhWMhTjQzsU)).

# A simple heap

A heap is a (conceptually) tree-based data structure used to quickly access and
maintain access to the maximum or the minimum of a collection of values. It
satisfies the _heap property_, that is (for a maximum heap) the label of a node
is bigger than or equal to that of its children. The following typeclass
summarises the common operations on heaps.

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

This typeclass is a bit mouthful because many of its operations are
inter-definable which is reflected in the `MINIMAL` pragma. The `Elem`
type-family (enabled by `TypeFamilies`) associated with the class gives the type
of the element of that heap. We could have equally used `MultiParamTypeClasses`
and `FunctionalDependencies` extensions to establish the same container-element
relationship. Because I will be using type families in a moment for different
reasons anyway and because I find that `Elem heap` has less cognitive overhead
than remembering a functional dependency between type variables, I used a
type-family here.

The most important heap operations in this post are `merge` and `decompose`. The
former merges two heaps and is used to directly or indirectly implement all
other operations for a leftist heap. The latter in one step gives the maximum of
a list and also a new heap with the maximum removed. This is then used to
implement the `findMax` and `deleteMax` operations which along with `insert` are
the most used functions provided by the interface.

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

This is possibly one of the simplest heap implementations. Insertion is $O(1)$,
merging is $O(n)$, conversion from a list is $O(1)$, decomposing (and
subsequently finding and deleting the maximum) is $O(n)$. If it wasn't for that
last linear time complexity, it would have been a perfectly heap implementation,
alas here we are.

This implementation is _obviously_ correct. As such any other correct heap
implementation should be _functionally equivalent_ to it. That is to say if we
perform the same operations on both this heap implementation and also on another
one, the maximum of both heaps should be the same. We'll use this reference
equivalence by performing simulations on this and other implementations and see
if they are functionally equivalent.

# A leftist heap

We now look at the data structure that we really care about. The leftist heap is
both conceptually and implementation-wise a tree. We use the following data type
for the unverified implementation.

```haskell
data LeftistHeap a = Leaf | Node a Int (LeftistHeap a) (LeftistHeap a)
```

The tree structure is standard except for the `Int` parameter of the node. This
is the _rank_ of the tree. The rank of the tree is the smallest distance it
takes to reach a `Leaf` node. The rank of a `Leaf` node is 0 and rank of a
`Node` is the minimum of its children ranks plus 1.

The leftist heap, in addition to the heap property, has the _leftist property_.
If the rank of a given node is $R$ that is the distance from that root to the
right-most `Leaf`. That is the rank of any left child is at least as big as a
right child.

What is the relationship between the rank and the size of a tree. A first
question is how many elements there needs to be in the tree if its rank is $R$.
If you want to figure this out for yourself, stop reading now. If the rank of a
tree is $R$, then it must be the case that each path from the root has $R$
`Node`s, otherwise the rank of the tree would be fewer. This means the tree has
at least $2^{R} - 1$ elements. Then the followup question is, if a tree has $N$
elements, what is its maximum rank? This is the place to stop to figure out on
your own. Well, we know that the rank imposes a lower bound on the tree size, so
conversely, the tree size should impose a maximum on the rank. We have
$2^{\mathit{MaxR}} - 1 \leq N \lt 2^{\mathit{MaxR} + 1} - 1$, so $\mathit{MaxR}
\leq \floor{\log{N} + 1} < R + 1$.

It has $O(\log{n})$ complexity for insertion and deleting the maximum, while
maintaining $O(1)$ complexity for finding the maximum. Building a heap out of a
list is $O(n)$. Asympotically these are the same for the array-based binary heap
implementation. But we can do one better. While the binary heap has $O(n)$
complexity for merging, it's only $O(\log{n})$ for the leftist heap. In fact, it
is the reason why insertion and deleting the maximum are $O(\log{n})$.

Why bother with the leftist heap at all? It's operations are persistent (hence
better suited for multi-threaded computation); more generally it is purely
functional; it is conceptually and implementation-wise a tree; and more
resilient against off-by-one errors. Why bother with the array-based binary
heap? Operations are in place; it probably performs better in practice because
arrays tend to have good locality of reference (this is a hunch, I haven't
actually looked at its cache behaviour and I'd like to be proven wrong); it is
the best-known implementation, so easier to communicate.

## Merging two heaps

## Every other operation

Once we can merge, we can do everything else. Maximum is maintained at the root,
so accessing it is easy. The `decompose` operation returns the maximum along
with the rest of the heap with the maximum removed. It accesses the root and
merges its two children (which are themselves leftist heaps). Insertion creates
a singleton heap out of the value being inserted and merges it into the heap.

Conversion from a list is more interesting. The obvious implementation is to
fold over the list of elements and insert them into the heap, this turns out not
to be the most efficient way. If we instead turn each element into a singleton
heap and repeatedly merge two heaps at a time (with multiple passes) until one
heap is left, conversion happens in linear time. This is the default
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
Assume for simplicity that there are $2^R$ elements in the heap. Then in the
first pass we do $2^{R-1}$ $O(\log{2})$ operations. In the next pass, we do
$2^{R-2}$ $O(\log{4})$ and in the next one $2^{R-3}$ $\log{8}$ operations and so
on. So the overall complexity is $O(\sum{\log{(2^i\,)} \; 2^{R-i}}\,)$ which is
roughly $O(\sum{i \; 2^{R-i}}\,)$ and that is $O(2^R)$ and roughly $2^R$.  That
is the number of elements we started with, so conversion from list is done in
linear time.

# Verifying the leftist property

# Verifying the heap property

# Simulating heap operations

# Conclusion

# Full program
