---
title: Cellular Christmas Tree
postType: Technical
inWhich: we create a program displaying a Christmas tree from a single dot on an
  infinite tape using two cellular automata computed with comonads as used in
  Haskell. You can also call it yet-another-comonad-tutorial if you like.
---

This post is late, the season has passed, and I am writing this in one of the
least Christmasy places. Yet I like this little diversion so much that I'll
share it with you. Just look at how heart-warming this looks.

![Cellular Christmas Tree](/images/cellular-christmas-tree/xmas-tree.gif "Cellular Christmas Tree GIF"){.left}

If you're in the midst of a paper crisis, one of the best ways to procrastinate
is to learn something you haven't got around to for ages and doesn't in any way
contribute towards your paper. In my case, this was comonads.

It's not that I didn't know what comonads were. They are the dual concept of
monads in category theory, but this sort of lost its meaning once I realised I
don't know what a monad is.

After some digging and head-scratching, I realised comonads are good for
computing from *context*. In comonad explanations, you often find zippers,
multi-dimensional arrays, and streams as example instances, used in everything
from cellular automata to dataflow analysis. In this post, we only focus on
zippers to implement cellular automata.

Below, we first give an overview of the comonad typeclass in Haskell and write
out the instance for zippers. Then using the primitives of the typeclass, we
build a blinking Christmas tree and briefly look at a way of displaying it
finitely.

## Comonad typeclass primer

Although hearing comonads are the dual of monads at a categorical level didn't
help me conceptually, it helps me remember the signatures of its primitives.
For `return`, `bind`, and `join` of monads, there are `coreturn`, `cobind`, and
`cojoin` in comonads. The function arrows in the signature of these functions
are helpfully reversed. As one might expect, we can define `cobind` in terms of
`cojoin`. This is what they mean when they say comonads are just the dual
concept of monads, though without further explanation it is not as helpful as
some think! These functions are also given different names in Haskell,
`extract`, `extend`, and `duplicate` respectively. Whether these names make the
concept clearer or more confusing is a source of lively discussions.

```haskell
class Functor w => Comonad w where
  extract   :: w a -> a
  duplicate :: w a -> w (w a)
  extend    :: (w a -> b) -> w a -> w b
  extend f cm = fmap f (duplicate cm)
```

I know the definition is not terribly exciting after I gave it away in the
explanation. Perhaps the interesting bit is the simple definition of `extend` in
terms of `duplicate`. In particular, `f` in `extend` does some form of
*reduction* from the *context* and this is applied over duplicate of a comonad
instance.  Intuitively, `extend`'s job is to use `f` to compute new focus
points. This implies that `duplicate`'s function is to encapsulate the instance
within itself with different points in focus.

OK. I know. That explanation was less than intuitive. Let's see an instance
instead. The data structure of interest today is a *zipper*. You can think of it
as a list with a focus[^1]. It is defined along with helpful functions to
change the focus point.

```haskell
data Zipper a = Zipper [ a ] a [ a ] deriving Functor

left, right :: Zipper a -> Zipper a
left  (Zipper (l:ls) a rs) = Zipper ls l (a:rs)
right (Zipper ls a (r:rs)) = Zipper (a:ls) r rs
```

The middle parameter is the focus point and we have bunch of elements to the
left and right. We'll use zippers with infinite number of elements, but there
isn't a fundamental reason that has to be the case elsewhere. So you can think
of a zipper as an infinite tape with a focus and `left` & `right` functions as
shifting the tape.

Let's get to the comonad instance for `Zipper`. The `extract` function is
pleasingly dull and extracts the focus of the zipper. The `duplicate` function
is slightly more interesting. It makes shifted copies of the zipper in a zipper
where the number of shifts is determined by the direction and distance from the
focus point of the enclosing zipper[^2].

```haskell
instance Comonad Zipper where
  extract (Zipper _ a _) = a
  duplicate u = Zipper (tail $ iterate left u) u (tail $ iterate right u)
```

If you're still unsure about zippers and comonads there are better explanations
of them than that of mine (such as those by [Dan
Piponi](http://blog.sigfpe.com/2007/01/monads-hidden-behind-every-zipper.html)
and [Bartosz Milewski](https://bartoszmilewski.com/2017/01/02/comonads/)) which
you can jump in before coming back for the Christmas tree.

## Cellular automata for Christmas tree

Now that we are equipped with the full power of comonads, we can proceed to
animate a Christmas tree---admittedly, an underwhelming use case.

We will use two cellular automata. First to grow the tree and then another to
make it blink. We need an initial configuration to start the whole process and
as promised, it is a single dot on an infinite tape.

```haskell
initConf = Zipper (repeat 0) 1 (repeat 0)
```

Any respectable Christmas tree would have at least two dimensions and this
zipper represents only the top of the tree. We heighten it by evolving this
initial configuration via the reduction `grow` and stack the generations one
below the other[^3].

```haskell
grow :: Zipper Int -> Int
grow (Zipper (l:_) a (r:_)) = if l == r then 0 else 1
```

Here `grow`'s type signature corresponds exactly to that expected by the
`extend` function. Functionally, it is the XOR of the left and right neighbours.

If you evolve some number of generations, stack successive generations one after
another, and print it on your terminal, you obtain a fine looking ASCII tree. In
each generation, the farthest left and right `1`-cells have one farther
`0`-cell. This cell, then, has a `0`-cell and a `1`-cell as its neighbours. In
the next generation, these `0`-cells become `1`-cells and we get a triangular
shape for stacking configurations. In a terminal, since the height of a letter
is often longer than its width, we get a nice top angle suitable for a tree.
Every generation that is a power of 2 has only `1`-cells between its farthest
edges making a base for our tree.

Now that we have a tree (of infinite height), we can focus on making it blink
using the `blink` reduction.

```haskell
blink :: Zipper Int -> Int
blink (Zipper _ 0 _) = 0
blink (Zipper (l1:l2:_) a (r1:r2:_)) = 1 + (l1 + l2 + a + r1 + r2) `mod` 3
```

It is constructed so that `0` is treated as dead space and maps to itself
regardless the context and no other value ever maps to it (by adding one to a
non-negative expression). We compute modulo three of a five-cells-wide window
which gives us sufficiently "random" blinking pattern and three symbols to shift
through.

With these two reductions, all we need is `grow` to generate as many
configurations as we like the height of the tree to be and `blink` to animate
it. The generations produced using `grow` will act as initial configurations of
the automaton with the transition function `blink`. We can exploit Haskell's
laziness to generate a comprehensive tree and worry about height, width, and
number of animation frames once we want to display it.

```haskell
trees :: [ [ Zipper Int ] ]
trees = transpose $ iterate (extend blink) <$> tree
  where
  tree = iterate (extend grow) initConf
```

Repeated application of `grow` through `iterate` produces tapes to stack and we
use each of those configurations with `blink` to animate. All `transpose` gives
is a list of frames of trees instead of a list of lists of configurations.

## Displaying infinity

This is the trivial bit of it. Since the tree is vertically symmetric on the
zipper focus, we can take equal number of items on each side to set the width
and take as many tapes as we want to set the height.

```haskell
frame :: Int -> Int -> [ Zipper a ] -> [ [ a ] ]
frame halfWidth height zs = take height $ frameConfig <$> zs
  where
  frameConfig (Zipper ls a rs) =
    reverse (take (halfWidth - 1) ls) ++ a : take (halfWidth - 1) rs
```

Asterisks, pluses, and x make better tree ornaments than integers.

```haskell
display :: Int -> Char
display 0 = ' '
display 1 = 'x'
display 2 = '*'
display 3 = '+'
```

Bringing all of this together we can print frames *forever* (though `blink`
behaves periodically) with some UNIX trickery to clear the terminal and
inserting delays so our petty human eyes can follow the blinking.

```haskell
main = do
  let (halfWidth, height) = (17, 16)
  forM_ trees $ \fr -> do
    putStrLn (intercalate "\n" (fmap display <$> frame halfWidth height fr))
    threadDelay 500000
    putStr "\ESC[2J" -- UNIX trickery to clear the terminal.
```

## Concluding thoughts

Here it is, another comonad tutorial. I don't think it is any better than the
others, but it produces something different. A good exercise for strengthening
your comonad-fu would be coding [Conway's Game of
Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life#Rules) with the
rules encoded as a reduction and the board represented as a two dimensional
array. Perhaps you pursue understanding it categorically; in that case, come and
tell me about it.

Happy past, present, and future holidays.

The full program is below for your convenience.

```haskell
{-# LANGUAGE DeriveFunctor #-}

module Main where

import Data.List (transpose, intercalate)

import Control.Concurrent (threadDelay)
import Control.Monad (forM_)

class Functor w => Comonad w where
  extract   :: w a -> a
  duplicate :: w a -> w (w a)
  extend    :: (w a -> b) -> w a -> w b
  extend f cm = fmap f (duplicate cm)

data Zipper a = Zipper [ a ] a [ a ] deriving Functor

left, right :: Zipper a -> Zipper a
left  (Zipper (l:ls) a rs) = Zipper ls l (a:rs)
right (Zipper ls a (r:rs)) = Zipper (a:ls) r rs

instance Comonad Zipper where
  extract (Zipper _ a _) = a
  duplicate u = Zipper (tail $ iterate left u) u (tail $ iterate right u)

initConf = Zipper (repeat 0) 1 (repeat 0)

grow :: Zipper Int -> Int
grow (Zipper (l:_) a (r:_)) = if l == r then 0 else 1

blink :: Zipper Int -> Int
blink (Zipper _ 0 _) = 0
blink (Zipper (l1:l2:_) a (r1:r2:_)) = 1 + (l1 + l2 + a + r1 + r2) `mod` 3

trees :: [ [ Zipper Int ] ]
trees = transpose $ iterate (extend blink) <$> tree
  where
  tree = iterate (extend grow) initConf

frame :: Int -> Int -> [ Zipper a ] -> [ [ a ] ]
frame halfWidth height zs = take height $ frameConfig <$> zs
  where
  frameConfig (Zipper ls a rs) =
    reverse (take (halfWidth - 1) ls) ++ a : take (halfWidth - 1) rs

display :: Int -> Char
display 0 = ' '
display 1 = 'x'
display 2 = '*'
display 3 = '+'

main = do
  let (halfWidth, height) = (17, 16)
  forM_ trees $ \fr -> do
    putStrLn (intercalate "\n" (fmap display <$> frame halfWidth height fr))
    threadDelay 500000
    putStr "\ESC[2J" -- UNIX trickery to clear the terminal.
```

[^1]: In fact, the connection between a list and a zipper goes way deeper. The
latter is the differentiation of the former. Try to wrap your head around that!
Or don't and read (parts of) the wonderfully titled paper [*"Clowns to the left
of me, jokers to the
right"*](https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf) by Conor
McBride.

[^2]: This is a common pattern. Streams and non-empty lists for example follow
pretty much the same implementation for `duplicate`. Here are the instances
without further explanation.

    ```haskell
    instance Comonad Stream where
      extract (Cons x _) = x
      duplicate s@(Cons _ xs) = Cons s (duplicate xs)

    instance Comonad NonEmpty where
      extract (x :| _) = x
      duplicate n@(_ :| xxs) = n :| case of xxs
        [] -> []
        x:xs -> duplicate (x :| xs)
    ```

[^3]: I admit that stacking one dimensional configurations is a bit awkward and
perhaps a two dimensional one is more natural. Well, it is less fun that way,
but if you insist you can use a two dimensional array to produce a similar tree.
Here is an example declaration of such an array from Dominic Orchard's paper
titled [*"A notation for
Comonads"*](https://www.cs.kent.ac.uk/people/staff/dao7/publ/codo-notation-orchard-ifl12.pdf).

    ```haskell
    data CArray i a = CA (Array i a) i
    ```

    You might get a two dimensional array that would help for our purposes with
    a type such as `CArray (Int,Int) Int`.
