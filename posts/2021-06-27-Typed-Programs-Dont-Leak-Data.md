---
title: Typed Programs Don't Leak Data
postType: Technical
inWhich: we turn privacy violations into compile-time errors in a simple
  imperative language embedded in Haskell and make GHC enforce it in style
  using GADTs.
published: false
---

Private data should remain private. The goal is obvious, but how to achieve it
is less so.

First, it is a deeply global problem. Private data can enter a system through a
fancy frontend and make its way deep into the jungle of backend services only to
be logged into a file and read by someone who is not supposed to. It is not
practical for people to audit a large system end-to-end.

Second, it is not amenable to testing. The most _explicit_ cases of leakage such
as
```
publicStatus := privateMaritalStatus
```
can perhaps be tested, but how about the more _implicit_ and elusive forms of
leakage such as
```
if privateMaritalStatus = "single" {
  publicStatus := "available"
} else {
  else publicStatus := "complicated"
}
```
where private data doesn't physically move to the public status, but by
observing the public status, we can figure something out about the private data.

The nightmare doesn't end there. There are subtler ways of leaking data such as
termination, execution time, and exceptions. Perhaps the most famous example is
figuring out passwords by measuring the time it takes for a program to reject
candidate passwords. The longer it it takes, more of the prefix we know.

There are multitude of ways of mitigating these problems both dynamic and
static. In this post, I'll focus on one productive static approach, namely we'll
look at type systems that makes private data leakage impossible. Let's get into
it.

All the Haskell necessary imports and Haskell extensions can be found [at the
end of this post](#full-program) as well in [this repository]().

## A simple imperative language

As this is a blog post, we'll use the most contrived language possible that
demonstrates all the major ideas. First, we define everything using simple types
that does not make use of any fancy type machinery.

Our expression language has integer literals, variables, and addition.

```haskell
data Variable = Variable String

infixr 6 :+
data Exp where
  EInt :: Int -> Exp
  EVar :: Variable -> Exp
  (:+) :: Exp -> Exp -> Exp
```

Our little imperative language has assignment, sequencing, if-then-else
statements, and while loops.

```haskell
infixl 5 :=
infixl 4 :>>
data Cmd where
  (:=)  :: Variable -> Exp -> Cmd
  (:>>) :: Cmd -> Cmd -> Cmd
  ITE   :: Exp -> Cmd -> Cmd -> Cmd
  While :: Exp -> Cmd -> Cmd

newtype Program = Program Cmd
```

Here's a simple program in this language

```haskell
simpleProgram :: Program
simpleProgram = Program $
  x := EInt 42 :>>
  ITE (EVar x)
    (While (EVar y) $
      y := EVar y :+ EInt (-1) :>>
      x := EVar x :+ EInt 1)
    (y := EInt 24)
  where
  x = Variable "x"
  y = Variable "y"
```

In more traditional syntax, this program corresponds to the following:

```
x := 42;
if (x) {
  while (y) {
    y := y - 1;
    x := x + 1;
  }
} else {
  y := 24;
}
```

At this point, I should write an evaluator function to give semantics to this
language, but there is nothing interesting about the dynamic semantics. The
intuitive evaluation of the language is the right one. The only oddity is that
we treat `0` as false and any other number as true when an expression is used as
a conditional expression.

## Typing our language

Now that we are acquainted with the language, let's prevent private data from
leaking.

### Security levels

Let's first distinguish private from public. We'll use natural numbers to do
that. The higher the values, the more private they are. All variables in our
language shall have intrinsic security levels.

```haskell
type Level = Nat

newtype Variable (l :: Level) = Variable String

public :: Variable 0
public = Variable "public"

private :: Variable 999
private = Variable "private"
```

### Expressions

Our expression language will remain the same, but the expressions will reflect
how private they are in their types.

For variable expressions, the obvious choice is to use the security level of the
underlying variable. The literals will all be public, i.e., they all have the
security level 0. Finally, for plus, we'll be conservative and pick the more
private security level. A folder that contains top secret intelligence and a
pizza flyer still cannot be handed to a pizza lover without security clearance.

```haskell
infixr 6 :+
data Exp (level :: Level) where
  EInt :: Int -> Exp 0
  EVar :: Variable level -> Exp level
  (:+) :: Exp level1 -> Exp level2 -> Exp (Max level1 level2)
```

Another way of writing these constructors would be using inference rules. `e :
l` means `e` has a security level `l` and `v : l` means the intrinsic security
level of the variable `v` is `l`. (I take some liberties with the notation)

```
  ----------
  EInt n : 0

    v : l
  ----------
  EVar v : l

  e1 : l1      e2 : l2
  --------------------
  e1 :+ e2 : max l1 l2
```

Here's a simple expression where the maximum computation is done for us behind
the scenes.

```haskell
simpleExp :: Exp 999
simpleExp = EVar public :+ EVar private
```

### Commands

The commands are where information flow happens and where our type system gets
interesting. Here they are

```haskell
infixl 5 :=
infixl 4 :>>
data Cmd (level :: Level) where
  (:=)  :: (le <= lx) => Variable lx -> Exp le -> Cmd lx
  (:>>) :: Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
  ITE   :: (lb <= Min l1 l2) => Exp lb -> Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
  While :: (lb <= l) => Exp lb -> Cmd l -> Cmd l
```

Structurally, it is identical to the simple commands. We have the same
constructors with the same number of arguments. However, this definition is
different in two different ways.

1. Each command now carries a security level. More precisely, they carry the
   level of the most public variable that was assigned in the command.
2. Constructors for assignment, conditional, and while statements now require
   conditions on the security levels of their parameters.

In the end, we don't care about the security level of a command, it is only
necessary to bar bad data flows. So it can be hidden away once we construct the
program with the help of an existential type.

```haskell
data Program = forall l. Program (Cmd l)
```

We now go over each of these constructors one by one. Just as we did for
expressions, we present the inference rule corresponding to each constructor.
`c : l` means that the lowest security level that the command `c` assigns to is
`l`.

#### Assignment

The assignment rule is the most fundamental as it is the only way in our
language that can leak private data.

```haskell
(:=) :: (le <= lx) => Variable lx -> Exp le -> Cmd lx
```

The equivalent inference rule:

```
  v : lv    e : le    le <= lv
  -----------------------------
          v := e : lv
```

An assignment has only one variable in it, so the most public variable it
assigns to is the variable being assigned. However, to construct an assignment
at all, the expression must be less private than the variable.

This is enough to ban all private data leaking through explicit flows. For
example, the following program is fine because `public` has a lower security
level (i.e., more public) than `private`.

```haskell
simpleAssignmentOK = Program $
  private := EVar public
```

However, if we attempt to go in the other direction, we'll get a type error.

```haskell
simpleAssignmentKO :: Program Cmd
simpleAssignmentKO = Program $
  public := EVar private
```

Particularly, GHC has the following to say about this program:

```
Couldn't match type ‘'False’ with ‘'True’ arising from a use of ‘:=’
```

I grant you that this is not the most obvious error message. But at least we
have a compile-time error instead of leaking private data! Substituting the
security levels, we have `999 <= 0` which is a shorthand for `999 <=?  0 ~ True`
and GHC simplifies `999 <=? 0` to `False`. This is why the error message says
`False` and `True` do not match.

#### Sequencing

The most public variable assigned in a sequence of two commands of course
belongs to the subcommand that has the more public assignment in it.

```haskell
(:>>) :: Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
```

The equivalent inference rule:

```
  c1 : l1       c2 : l2
  ---------------------
  c1 :>> c2 : Min l1 l2
```

Two commands in sequence are well-typed if and only if both of the subcommands
are well-typed. For example, the following sequence of two assignments is
alright.

```haskell
tempAssignmentOK :: Program Cmd
tempAssignmentOK = Program $
  temp := EVar public :>>
  private := EVar temp
  where
  temp = Variable @5 "temp"
```

The security level of the assignments are `Min 5 0` and `Min 999 5`, so the
overall security level for the sequenced command is `Min 0 5` which is just `0`,
i.e., the security level of `public` which is indeed the most public variable
assigned in the program.

#### If-then-else

It is time to tackle the more mysterious implicit flows that happen as a result
of a conditional write to some public data based on a private one.

```haskell
ITE :: (lb <= Min l1 l2) => Exp lb -> Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
```

The equivalent inference rule:

```
           e : lb
          c1 : l1
          c2 : l2
      lb <= Min l1 l2
  -----------------------
  ITE e c1 c2 : Min l1 l2
```

The reasoning for the overall security level of a conditional statement is same
as that for sequencing. The most public level assigned in the overall statement
must come from the more public subcommand. Unlike sequencing, we know that only
one of the branches will be taken but we cannot know which one at compile time,
so we pessimistically account for both cases.

This rule also comes with a requirement that needs to be satisfied. The security
level of the conditional expression must be less than those of both branches.
This prevents implicit flows and explains why we carry the security level of
the most public security level commands assign to. If the security level of the
expression was higher than the lowest level assigned in one of the branches,
then a more public variable's value would be in part determined by a private
one. Thus, by observing the more public value, we could deduce something about
the private value. However, the condition ensures that only more public data can
influence private data. This is safe because whoever has access to the more
private data would also have to the public one.

The explanation was a mouthful, but the examples make point clearer.

```haskell
implicitPublicFlowOK :: Program Cmd
implicitPublicFlowOK = Program $
  ITE (EVar public)
    (public := EInt 42)
    (private := EVar public)
```

The conditional expression in this program is public. In the then branch, we
assign to a public data which is always safe. In the else branch, we assign
private data, but this is fine too since by observing the result of `private`,
we can only make a conclusion about `public` which we are allowed to anyway.

The following program, on the other hand, fails with the same `True` is not
`False` error:

```haskell
implicitPrivateFlowKO :: Program Cmd
implicitPrivateFlowKO = Program $
  ITE (EVar private)
    (public := EInt 42)
    (private := EVar public)
```

This program fails because once executed, if we observe the value of `public`
not to be `42`, the fact that `private` is non-zero is leaked. Luckily, since
`private` is more private than `public`, the conditional statement is ill-typed.

The typing rules for conditionals also come with a limitation. It bans programs
that cannot leak private data.

```haskell
implicitPrivateFlowOKKO :: Program Cmd
implicitPrivateFlowOKKO = Program $
  ITE (EVar private)
    (public := EInt 42)
    (public := EInt 42)
```

This program is illegal according to our typing rules because there is an
implicit flow from security level `999` to `0` (in two different ways in fact!),
but it does not actually leak data. By observing the value of `public` after the
conditional, we cannot deduce anything about `private` because the assignment to
`public` is consistent in both branches.

This particular example looks easy to detect, but in general, it requires
program equivalence which would make typechecking undecidable.

#### While loop

Uncharacteristically, while loop rule is simpler than the one for if-then-else
statements.

```haskell
While :: (lb <= l) => Exp lb -> Cmd l -> Cmd l
```

The equivalent inference rule:

```
      e : lb
      c : l
     lb <= l
  -------------
  While e c : l
```

The minimum assignment level can only come from the only subcommand of the while
loop.

The requirement for constructing a while loop is for the conditional
expression's security level to be more public than the most public level
assigned in the loop body. The reasoning is precisely the same as the one for
if-then-else statements.

Now that we have the while loop, let's look at the least contrived program of
this post. We halve an even natural number by looping.

Let's first derive reusable increment and decrement operations. To do this we
derive a generic `adder` first.

```haskell
lemmaMax0 :: Max level 0 :~: level
lemmaMax0 = Refl

adder :: forall level. Int -> Variable level -> Cmd level
adder i var | Refl <- lemmaMax0 @level = var := EVar var :+ EInt i
```

This looks more complicated than one initially expects. The body of the adder is
simple, we offset the given variable's value with `i` and assign back to the
variable. But what about that `lemmaMax0` and `Refl`. Long story, short the
assignment in question does not have access to a concrete level, it works for
any level, so GHC has to do some symbolic reasoning.

In particular, it needs to prove that `Max level 0 <= level`. This is always
true, but not obvious GHC. I prove a stronger property in `lemmaMax0`, namely
`Max level 0` is exactly `level`. The proof is by reflexivity. Normally, GHC
cannot do this on its own, so you need to teach it. I could have reinvented
basic arithmetic, but I felt lazy and added a typechecker plugin that lets GHC
in on some basic arithmetic facts. These plugins are incredibly cool, but very
much scope of this post. The plugin I used is in
[ghc-typelits-extra](https://github.com/clash-lang/ghc-typelits-extra).

Now that we have this lemma, I simply pattern match on it which simplifies the
`Max level 0 <= level` proof obligation to `level <= level` and GHC is clever
enough to work that one out.

After the small detour, the actual increment and decrement operations are
trivial.

```haskell
inc, dec :: Variable level -> Cmd level
inc = adder 1
dec = adder (-1)
```

We are now ready to halve an even natural number and store its value in
`private`.

```haskell
halveCovertKO :: Program Cmd
halveCovertKO = Program $
  finished := EInt 0 :>>
  private := EInt 0 :>>
  While (EVar privCounter)
    (dec privCounter :>>
     dec privCounter :>>
     inc private) :>>
  inc finished
  where
  finished = Variable @0 "finished"
  privCounter = Variable @42 "privCounter"
```

The conditional of the while loop is just as private as the variables
incremented and decremented in its body. Hence, the program does not leak data,
or does it?

## Plugging covert channels

The natural number halving program above does not leak data explicitly or
implicitly, but it leaks some data through covert channels. We can observe that
the program terminates because we can observe the value of `finished`. Knowing
that the program terminated leaks the fact that `privCounter`'s original value
was either zero or odd. We shouldn't be able to deduce that since this counter
is private.

Fortunately, not all is lost. We can plug this covert channel with a minor
modification to the while constructor.

```haskell
While :: Exp 0 -> Cmd l -> Cmd l
```

The equivalent inference rule:

```
      e : 0
      c : l
  -------------
  While e c : l
```

This chance necessitates loop conditionals to be public. It also dispenses with
the conditional expression being more public than the most public variable
assigned in the body because this always holds when the conditional expression
is public.

This easily bars the halving program because it both modifies private variables,
but does it cover all cases of non-termination-based private data leakage? If the
program terminates, we learn that the conditional expression hit zero. This only
tells us about the data involved in that expression, so if all of that is public
anyway, we cannot possibly leak data.

### Expressivity

This change, sadly, lands two more blows to expressivity.

First, if we initialise `privCounter` before the while loop to a positive even
number, the program always terminates and the program cannot leak data. However,
deducing this in general requires a solution to the halting problem.

Second, and more importantly, non-termination can only depend on public data.
For example, if we extended our language with arrays and had an array of
employees, we would wouldn't be able to loop over employees if the number of
employees was private.

Our saving grace is that we can get a lot done with terminating programs.
Reassessing the employee example, if we extend our language with `foreach` loops
that loops over the array directly, granted that we cannot make the array larger
as we iterate over them, the loop would always terminate. Consequently, we can
have a more relaxed constructor for `foreach` loops.

## Final words

The language we considered here is simple, but the literature on type-based
information-flow control is both wide and active. We already talked about how we
can enrich the language with `foreach` and improve expressivity while being
termination-sensitive. The same trick we used for while loops can also be
applied to exceptions to prevent other covert channels. [Language-Based
Information-Flow Security](https://dl.acm.org/doi/10.1145/1929553.1929564) by
Andrei Sabelfeld and Andrew Myers provide a good lay of the land. More
specifically, [Eliminating covert flows with minimum
typings](https://ieeexplore.ieee.org/document/596807) by Volpano and Smith
introduces termination-sensitive typing we presented as well as how to securely
employ exceptions.

The ulterior motive of this post was to show off how seamless type-level
programming in Haskell could be. At no point, I said "I wish I was using a full
dependently typed language" to myself. We even avoided reinventing mathematics
using employing typechecker plugins. That topic clearly deserves a post of its
own.

You might be bit disappointed if you're a Haskell developer looking to employ
static IFC in your code. One remedy might be the [LIO monad available in
Hackage](https://hackage.haskell.org/package/lio) which takes a similar approach
but is dynamic. If you're after no runtime cost, Chapter 6 of [Information Flow
Enforcement in Monadic
Libraries](https://dl.acm.org/doi/10.1145/1929553.1929564) provides a monad
transformer in Haskell that employs the same ideas presented in this blog post
to statically enforce information-flow properties.

Finally, the intuition presented in this blog post about why our type system is
sound is no substitute for a formal proof. The most beautiful definition that
captures the desired property is called _non-interference_ which simply says
private data does not interfere with public data in a formal manner. This
definition is far reaching, but that too deserves a thorough treatment of its
own. That and the proof can be found in [A sound type system for secure flow
analysis](https://core.ac.uk/download/pdf/36700757.pdf) by Volpano, Irvine, and
Smith. This is also the paper that introduced the type system we considered.

## Full program

```haskell
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}

{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module VolpanoSmith where

import GHC.TypeLits (Nat, type (<=))
import GHC.TypeLits.Extra (Max, Min)
import Data.Kind (Type)
import Data.Data (type (:~:)(Refl))

--------------------------------------------------------------------------------
-- Basic language without Information-Flow Security enforcement
--------------------------------------------------------------------------------

newtype Variable0 = Variable0 String

infixr 6 :+.
data Exp0 where
  EInt0 :: Int -> Exp0
  EVar0 :: Variable0 -> Exp0
  (:+.) :: Exp0 -> Exp0 -> Exp0

infixl 5 :=.
infixl 4 :>>.
data Cmd0 where
  (:=.)  :: Variable0 -> Exp0 -> Cmd0
  (:>>.) :: Cmd0 -> Cmd0 -> Cmd0
  ITE0   :: Exp0 -> Cmd0 -> Cmd0 -> Cmd0
  While0 :: Exp0 -> Cmd0 -> Cmd0

type Program0 = Cmd0

simpleProgram :: Program0
simpleProgram =
  x :=. EInt0 42 :>>.
  ITE0 (EVar0 x)
    (While0 (EVar0 y) $
      y :=. EVar0 y :+. EInt0 (-1) :>>.
      x :=. EVar0 x :+. EInt0 1)
    (y :=. EInt0 24)
  where
  x = Variable0 "x"
  y = Variable0 "y"

--------------------------------------------------------------------------------
-- Privacy enforcing programs
--------------------------------------------------------------------------------

type Level = Nat

newtype Variable (l :: Level) = Variable String

infixr 6 :+
data Exp (level :: Level) where
  EInt  :: Int -> Exp 0
  EVar  :: Variable level -> Exp level
  (:+) :: Exp level1 -> Exp level2 -> Exp (Max level1 level2)

infixl 5 :=
infixl 4 :>>
data Cmd (level :: Level) where
  (:=)  :: (le <= lx) => Variable lx -> Exp le -> Cmd lx
  (:>>) :: Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
  ITE   :: (lb <= Min l1 l2) => Exp lb -> Cmd l1 -> Cmd l2 -> Cmd (Min l1 l2)
  While :: (lb <= l) => Exp lb -> Cmd l -> Cmd l

data Program (cmd :: Level -> Type) = forall l. Program (cmd l)

--------------------------------------------------------------------------------
-- Example programs
--------------------------------------------------------------------------------

public :: Variable 0
public = Variable "public"

private :: Variable 999
private = Variable "private"

simpleExp :: Exp 999
simpleExp = EVar public :+ EVar private

simpleAssignmentOK :: Program Cmd
simpleAssignmentOK = Program $
  private := EVar public

  {-
simpleAssignmentKO :: Program Cmd
simpleAssignmentKO = Program $
  public := EVar private
  -}

tempAssignmentOK :: Program Cmd
tempAssignmentOK = Program $
  temp := EVar public :>>
  private := EVar temp
  where
  temp = Variable @5 "temp"

implicitPublicFlowOK :: Program Cmd
implicitPublicFlowOK = Program $
  ITE (EVar public)
    (public := EInt 42)
    (private := EVar public)

  {-
implicitPrivateFlowKO :: Program Cmd
implicitPrivateFlowKO = Program $
  ITE (EVar private)
    (public := EInt 42)
    (private := EVar public)
  -}

  {-
implicitPrivateFlowOKKO :: Program Cmd
implicitPrivateFlowOKKO = Program $
  ITE (EVar private)
    (public := EInt 42)
    (public := EInt 42)
  -}

implicitPrivateFlowOK :: Program Cmd
implicitPrivateFlowOK = Program $
  ITE (EVar private)
    (private := EInt 42)
    (private := EVar public)

lemmaMax0 :: Max level 0 :~: level
lemmaMax0 = Refl

adder :: forall level. Int -> Variable level -> Cmd level
adder i var | Refl <- lemmaMax0 @level = var := EVar var :+ EInt i

inc, dec :: Variable level -> Cmd level
inc = adder 1
dec = adder (-1)

halveOK :: Program Cmd
halveOK = Program $
  finished := EInt 0 :>>
  public := EInt 42 :>>
  While (EVar pubCounter)
    (dec pubCounter :>>
     dec pubCounter :>>
     inc public) :>>
  inc finished
  where
  finished = Variable @0 "finished"
  pubCounter = Variable @0 "pubCounter"

halveCovertKO :: Program Cmd
halveCovertKO = Program $
  finished := EInt 0 :>>
  private := EInt 42 :>>
  While (EVar privCounter)
    (dec privCounter :>>
     dec privCounter :>>
     inc private) :>>
  inc finished
  where
  finished = Variable @0 "finished"
  privCounter = Variable @42 "privCounter"

--------------------------------------------------------------------------------
-- Termination-sensitive privacy enforcing programs
--------------------------------------------------------------------------------

infixl 5 :==
infixl 4 :>>>
data Cmd' (level :: Level) where
  Skip'  :: Cmd' level
  (:==)  :: (le <= lx) => Variable lx -> Exp le -> Cmd' lx
  (:>>>) :: Cmd' l1 -> Cmd' l2 -> Cmd' (Min l1 l2)
  ITE'   :: (lb <= Min l1 l2) => Exp lb -> Cmd' l1 -> Cmd' l2 -> Cmd' (Min l1 l2)
  While' :: Exp 0 -> Cmd' l -> Cmd' l

adder' :: forall level. Int -> Variable level -> Cmd' level
adder' i var | Refl <- lemmaMax0 @level = var :== EVar var :+ EInt i

inc', dec' :: Variable level -> Cmd' level
inc' = adder' 1
dec' = adder' (-1)

halveOK' :: Program Cmd'
halveOK' = Program $
  finished :== EInt 0 :>>>
  private :== EInt 0 :>>>
  While' (EVar pubCounter)
    (dec' pubCounter :>>>
     dec' pubCounter :>>>
     inc' private) :>>>
  inc' finished
  where
  finished = Variable @0 "finished"
  pubCounter = Variable @0 "pubCounter"

  {-
halveCovertKO' :: Program Cmd'
halveCovertKO' = Program $
  finished :== EInt 0 :>>>
  private :== EInt 0 :>>>
  While' (EVar privCounter)
    (dec' privCounter :>>>
     dec' privCounter :>>>
     inc' private) :>>>
  inc' finished
  where
  finished = Variable @0 "finished"
  privCounter = Variable @42 "privCounter"
  -}

  {-
halveCovertOKKO :: Program Cmd'
halveCovertOKKO = Program $
  privCounter :== EInt 42 :>>>
  finished :== EInt 0 :>>>
  private :== EInt 0 :>>>
  While' (EVar privCounter)
    (dec' privCounter :>>>
     dec' privCounter :>>>
     inc' private) :>>>
  inc' finished
  where
  finished = Variable @0 "finished"
  privCounter = Variable @42 "privCounter"
  -}
```
