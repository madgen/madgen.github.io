---
title: Comonadic Cellular Christmas Tree
postType: Technical
inWhich: we create a program displaying a Christmas tree from a single dot on an
  infinite tape using two cellular automata computed with comonads as used in
  Haskell.
---

This post is late, the season has passed, and I am writing this in one of the
least Christmasy places on this planet. Yet I like this little diversion enough
that I'll share it with you.

If you're in the midst of a paper crisis, one of the best ways to procrastinate
is to learn something you haven't got around to for a long time and doesn't
contribute towards your paper in any way. In my case, that is comonads.

It's not that I didn't know what comonads were. They are the dual concept of
monads in category theory, but this sort of loses its meaning once you realise
you don't know enough category theory to understand what a monad is apart from
parroting *"a monad is just a monoid in the category of endofunctors"*.

Upon this realisation, after some digging you realise it is a way of computing
from context. In blog posts or papers explaining such computations you may also
find examples such as zippers, multi-dimensional arrays, and streams. We'll only
use zippers here.

In the rest of this post I will give an overview of the comonad class in Haskell
and write out the instance for zipper. Then using the functions defined by
primitives of the comonad class, we'll build a blinking Christmas tree.

## Comonad class primer

Although saying comonads are the dual concept of monads at a categorical level
does not help conceptually, knowing that is the case helps remembering the
signatures of its primitives. For `return`, `bind`, and `join` of monads, there
is a `coreturn`, `cobind`, and `cojoin` in comonads. The function arrows in the
signature of these functions are helpfully reversed. As one might expect, we can
define `cobind` in terms of `cojoin`. This is what they mean when they say
comonads are just dual concepts of monads, though without further explanation,
it is not as helpful as some think! They are also given different names,
`extract`, `extend`, and `duplicate`. Whether these names make the concept more
clear or confusing is a source of endless lively discussions.

```haskell
class Functor w => Comonad w where
  extract   :: w a -> a
  duplicate :: w a -> w (w a)
  extend    :: (w a -> b) -> w a -> w b
  extend f cm = fmap f (duplicate cm)
```

I know the definition is not terribly exciting after I gave it away in the
explanation. Perhaps the interesting bit is the simple definition of `extend` in
terms of `duplicate`. In particular, `f` in extend does some form of reduction
from the *context* and this is applied over duplicate of a comonad instance.
Intuitively, `extend`'s job is to use `f` to compute new focus points. This
implies that `duplicate`'s function is to encapsulate the instance within itself
with different points in focus.

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

The middle element is the focus point and we have bunch of elements to the left
and right. We'll use zippers with infinite number of elements, but there isn't a
fundamental reason that has to be the case elsewhere. So you can think of a
zipper as an infinite tape with a focus and `left` & `right` functions as
shifting the tape.

Let's get to the comonad instance for `Zipper`. The `extract` function is
pleasingly dull and extracts the focus of the zipper. The `duplicate` function
is slightly more interesting. It makes shifted copies of the zipper in a zipper
where the shifting is determined by the direction and distance from the focus
point of the resulting zipper[^2].

```haskell
instance Comonad Zipper where
  extract (Zipper _ a _) = a
  duplicate u = Zipper (tail $ iterate left u) u (tail $ iterate right u)
```

If you're still unsure about zippers and comonads there are better tutorials
than mine which you can jump in before coming back to the Christmas tree.
Examples include those by [Dan
Piponi](http://blog.sigfpe.com/2007/01/monads-hidden-behind-every-zipper.html)
and [Bartosz Milewski](https://bartoszmilewski.com/2017/01/02/comonads/).

## Cellular automata for Christmas tree

Now that we are equipped with full power of comonads, we can proceed to make a
Christmas tree (a rather underwhelming use case).

We will use two cellular automata. First to grow the tree and then another to
make it blink. We need an initial configuration to start the whole process and
as promised, it is a single dot on an infinite tape.

```haskell
initConf = Zipper (repeat 0) 1 (repeat 0)
```

Any respectable Christmas tree would have at least two dimensions and this
zipper represents only the top of the tree. We can deal with this by evolving
this initial configuration via the reduction `grow` and stack the generations
one below the other[^3].

```haskell
grow :: Zipper Int -> Int
grow (Zipper (l:_) a (r:_)) = if l == r then 0 else 1
```

Here `grow`'s type signature corresponds exactly to that expected by the
`extend` function. Functionally, it is the XOR of the left and right neighbours.

If you create 16 generations, stack successive generations one after another,
and print it on your terminal, you obtain a fine looking looking ASCII tree.
Here we use the fact that in each generation the farthest left and right `1`
values will have one farther cell with `0` and `1` as its neighbours. Hence, we
get a triangular shape after stacking them. Never mind me abusing the aspect
ratio of individual cells on the terminal to achieve a good top angle.

[image]

Now that we have a tree (of infinite height), we can focus on making it blink.
We will make this using the `blink` reduction.

```haskell
blink :: Zipper Int -> Int
blink (Zipper _ 0 _) = 0
blink (Zipper (l1:l2:_) a (r1:r2:_)) = 1 + (l1 + l2 + a + r1 + r2) `mod` 3
```

It is constructed so that `0` is treated as dead space and maps to itself
regardless the context and no other value ever maps to it (by adding one to a
non-zero expression). We compute modulo three of a five cells wide window which
gives us sufficiently "random" blinking pattern and three symbols to shift
through.

Now that we have our reductions, all we need to do it to use `grow` to generate
as many configurations as we like the height of the tree and use `blink` to
animate it. We can exploit Haskell's laziness to generate a comprehensive tree
and worry about height, width, and number of animation frames once it gets to
displaying it.

```haskell
trees :: [ [ Zipper Int ] ]
trees = transpose $ iterate (extend blink) <$> tree
  where
  tree = iterate (extend grow) initConf
```

Repeated application of `grow` through `iterate` produces tapes to stack and we
use each of those configurations with `blink` to animate. All `transpose` gives
is a list of frames of trees instead of a list of list of automata
configurations.

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

Although I like `Int`s as much as the next person, asterisks, pluses, and x
make better tree ornaments.

```haskell
display :: Int -> Char
display 0 = ' '
display 1 = 'x'
display 2 = '*'
display 3 = '+'
```

Bringing all of this together we can print frames *forever* (though it is a
periodic blinking behaviour) with some UNIX trickery to clear the terminal and
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

I attach the full program below for your convenience (and to show off with its
succinctness).

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

[^1]: In fact the connection between a list and a zipper goes way deeper. The
latter is the differentiation of the former. Try to wrap your head around that!
Or don't and read (parts of) the wonderfully titled paper [*"Clowns to the left
of me, jokers to the
right"*](https://personal.cis.strath.ac.uk/conor.mcbride/Dissect.pdf) by Conor
McBride.

[^2]: This is, in fact, a remarkably common pattern. Streams and non-empty
lists for example follow pretty much the same implementation pattern for
`duplicate`. Here are the instances without further explanation.

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
