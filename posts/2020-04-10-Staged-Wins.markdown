---
title: Staged Wins
postType: Technical
inWhich: we look at how effortless and profitable staged programming is in
  Haskell by (micro)benchmarking a regular expression interpreter and a staged
  compiler.
published: false
lastUpdated: 2020-09-01
---

As Haskell programmers, we live and die by the maxim "never do at runtime what
could be done at compile time". However, we (or at least me) almost exclusively
understand this as doing safety checks before runtime and do not appreciate the
full generality of this maxim. Although an optimising compiler will do much
computation before runtime, as a programmer we hardly ever have a say on the
matter.

The singular exception to this in many languages compiled or otherwise is
_metaprogramming_ where the purpose of our code is to generate code. If you
think about it, the concept is remarkably prevalent in many languages from C
preprocessor macros to abuses of C++ template system, from Ruby's highly
maleable object model to Java's class loader API. In fact, in Haskell alone, it
comes at least in three flavours: datatype-generic programming, Template
Haskell (henceforth TH), Typed-Template Haskell (henceforth TTH). The first is
convenient but comes at a runtime cost. The second one is performed at compile
time, but is unprincipled, potentially unhygienic, and effectively untyped. The
third restricts Template Haskell, but it achieves principled and well-typed
metaprograms with decent error messages!

As you might guess, TTH is the topic of this post. In particular, I take a naïve
regular expression recogniser and mindlessly apply TTH's quotations and splices
to answer two questions:

  1. Is it a pain to use TTH?
  2. What do I get out of going through this exercise?

The short answers are "not really" and "5x performance improvement in time".
However, the justification for the first answer is my highly subjective value
judgements with caveats and that for the second answer is backed only by
microbenchmarks on a few examples. So if your reputation is on the line, I
suggest you don't cite this blog post to support your argument. For that, I'd go
read articles, posts, and libraries by [Matthew
Pickering](https://mpickering.github.io), [Jeremy
Yallop](https://www.cl.cam.ac.uk/~jdy22/), and [Nada
Amin](https://namin.seas.harvard.edu/people/nada-amin).

In the rest of this post, we first quickly look at the regular expression
recogniser in question. We then stage it. Having these interpreted and staged
versions at hand, we quantitatively compare them using microbenchmarks and look
at the generated code to try to understand the performance difference. Finally,
we remark on the convenience of staging this program and conclude.

## A simple regular expression interpreter

We implement an interpreter just sophisticated enough to represent some
fictional phone number regular expression:
`0?\d\d\d\d(\w|-)*\d\d\d(\w|-)*\d\d\d`.  This would recognise `01234 567 890`
without the leading zero and with or without spaces at the designated places and
optionally with hyphens.

```haskell
data RegExp =
    Null
  | Char Char
  | RegExp :|: RegExp
  | RegExp :.: RegExp
  | Star RegExp
```

A number of useful regular expressions and primitives can be defined right away.

```haskell
digit :: RegExp
digit = foldr1 (:|:) (map Char ['0'..'9'])

whitespace :: RegExp
whitespace = Char ' ' :|: Char '\t'

-- r+
plus :: RegExp -> RegExp
plus re = re :.: Star re

-- r?
optional :: RegExp -> RegExp
optional re = re :|: Null
```

This is enough to represent our target regular expression.

```haskell
phoneNumber :: RegExp
phoneNumber =
  optional "0" :.:
  digit :.: digit :.: digit :.: digit :.: (Star whitespace :|: "-") :.:
  digit :.: digit :.: digit :.: (Star whitespace :|: "-") :.:
  digit :.: digit :.: digit
```

All there remains is to interpret these regular expressions. We interpret
regular expressions as `Matcher`s which are functions that takes a string input,
matches the regular expression to the longest prefix, and returns whatever
remains. If the string could not be matched at all, it returns nothing.

```haskell
type Matcher = String -> Maybe String

matchStar :: Matcher -> Matcher
matchStar matcher str =
  case matcher str of
    Just rest -> matchStar matcher rest
    Nothing -> Just str

interpret :: RegExp -> Matcher
interpret Null = pure
interpret (Char c) = \case
  (c' : rest) | c == c' -> Just rest
  _ -> Nothing
interpret (re1 :|: re2) = (<|>) <$> interpret re1 <*> interpret re2
interpret (re1 :.: re2) = interpret re1 >=> interpret re2
interpret (Star re)     = matchStar (interpret re)
```

The interpreter does not try to be clever. It compositionally interprets regular
expressions and combines them using monadic or applicative combinators.

A matcher defined by the interpreter is not quite what we are after as we want
exact matches. It is easy enough to make one of those out of a matcher.

```haskell
type Recogniser = String -> Bool

toRecogniser :: Matcher -> Recogniser
toRecogniser m str = m str == Just []
```

This is all there is to our regular expression interpreter.

## Staging the interpreter

So what treacherous road to optimisation is ahead of us? As it turns out, it is
a short and painless one. You only need to be aware of three things if you want
to use TTH: `TExpQ`, the quotation operator `[|| exp ||]`, and
and the splice operator `$$code`.

`TExpQ a` is the typed equivalent of TH's `Q Exp`. This already gives away that
we can only generate expressions with TTH. The type parameter `a` is the type of
the expression the generated code will evaluate to. This is entirely missing in
`Q Exp`, hence the "Typed" in TTH. This `TExpQ` constructor is, however, does
not have a terribly informative name, so I alias it with `Code`.

```haskell
type Code a = TExpQ a
```

The quotation operator (`[|| exp ||]`) takes an expression of type `a` and turns
it into `Code a`. The splice (`$$code`) operator goes the other way. In other
words, the former produces the code for some expression and the latter *in the
right context* evaluates that code.

If you then have something you want evaluated at compile time for sure, you just
write a function of the form `a -> Code b`. The `a` is what you want to get rid
of at runtime and the `Code b` is what you end up with as a result.

In our case, we had an interpreter with type `RegExp -> Matcher` and we want to
compile the regular expression away, so we'd like a function `RegExp -> Code
Matcher` instead. Well, how are we going to get there? Mechanically and
mindlessly!

Let's take the first case:

```haskell
interpret Null = pure
```

The `Matcher` is just `pure` and we want `Code Matcher`, so we just do `[|| pure
||]`.

```haskell
compile Null = [|| pure ||]
```

Okay, maybe we got lucky with that one. Let's try the second case.

```haskell
interpret (Char c) = \case
  (c' : rest) | c == c' -> Just rest
  _ -> Nothing
```

Remember that `Matcher` is a lambda, so that forces us to place the quotation
outside the lambda case expression and we are done.

```haskell
compile (Char c) =
  [||
    \case
      (c' : rest) | c == c' -> Just rest
      _ -> Nothing
  ||]
```

Now, you're thinking that base cases are always easy, so let's try a recursive
one.

```haskell
interpret (re1 :|: re2) = (<|>) <$> interpret re1 <*> interpret re2
```

We know the result is going to be `Code Matcher`, so we place the quotation
outsite the body once more.

```haskell
compile (re1 :|: re2) = [|| (<|>) <$> compile re1 <*> compile re2 ||]
```

However, this won't compile because `compile` has type `RegExp -> Code Matcher`.
Then, the expression inside the quotation needs to have the type `Matcher`.
This makes the recursive calls are ill-typed. They have type `Code Matcher`
instead of `Matcher`, but we already know how to go in this direction with a
splice. So, all we need is to wrap these recursive calls with it.

```haskell
compile (re1 :|: re2) = [|| (<|>) <$> $$(compile re1) <*> $$(compile re2) ||]
```

We are done once more. The next two recursive cases are treated similarly. So
overall, we end up with a compiler strikingly similar to the interpreter. Most
surprisingly, we exercised almost no brain cells along the way.

```haskell
compile :: RegExp -> Code Matcher
compile Null = [|| pure ||]
compile (Char c) =
  [||
    \case
      (c' : rest) | c == c' -> Just rest
      _ -> Nothing
  ||]
compile (re1 :|: re2) = [|| (<|>) <$> $$(compile re1) <*> $$(compile re2) ||]
compile (re1 :.: re2) = [|| $$(compile re1) >=> $$(compile re2) ||]
compile (Star re)     = [|| matchStar $$(compile re) ||]
```

Let's use it on an example. We first start a new file with a new module (this
bit is important and [an explanation will follow](#qualitative-remarks)). Then,
we see if the regular expression `"ab"` recognises the string `"ababababab"` in
the module.

```
resInterpreted = toRecogniser $ interpret $ Star "ab"
resCompiled    = toRecogniser $$(compile $ Star "ab")
```

## Microbenchmarks

Staging was easy enough, but what does it buy us? A general answer is difficult,
but here's one microbenchmark. We look at the speed at which the interpreted and
staged regular expression recognisers match
`0?\d\d\d\d(\w|-)*\d\d\d(\w|-)*\d\d\d` against the following:

```
04207999163
0420799916
04207 999 163
04207-999-163
04207 a99 163
04207    999    163
04207  0 999    163
4207    999    163
```

The `criterion` benchmarking results indicate a convincing ~5x win when compiled
with `-O1` and a ~%5 improvement with `-O0`.

![Microbenchmark results for -O0](/images/staged-wins/microbenchmarks-O0.png)

![Microbenchmark results for -O1](/images/staged-wins/microbenchmarks-O1.png)

### But why?

We have three questions to answer:

1. why does the compiled version un faster than the interpreted one even without
optimisations?
2. why does the compiled version benefit so much from optimisations, unlike the
interpreted version?

To understand the compiled version's success without optimisations, it is enough
to inspect the partially evaluated code. Passing the `-ddump-splices` and
`-ddump-to-file` GHC options yields a file with `Foo.dump-splices` extension
that contains the partially evaluated expressions in a module `Foo`. The
resulting splice is nearly 700 lines long (due to partially evaluating the
relatively complex phone number regex), but it is enough to look at only a few
lines.

```haskell
(((((((((((((((GHC.Base.<|>)
    <$>
      (\case
         (c'_a5jT : rest_a5jU) | ('0' == c'_a5jT) -> Just rest_a5jU
         _ -> Nothing))
   <*> pure)
  Control.Monad.>=>
    (((GHC.Base.<|>)
        <$>
          (\case
             (c'_a5jV : rest_a5jW) | ('0' == c'_a5jV) -> Just rest_a5jW
             _ -> Nothing))
       <*>
         (((GHC.Base.<|>)
             <$>
               (\case
                  (c'_a5jX : rest_a5jY) | ('1' == c'_a5jX) -> Just rest_a5jY
                  _ -> Nothing))
            <*>
              (((GHC.Base.<|>)
                  <$>
                    (\case
                       (c'_a5jZ : rest_a5k0) | ('2' == c'_a5jZ) -> Just rest_a5k0
                       _ -> Nothing))
                 <*> ...
```

We can see that this expression optionally looks for a `0` followed by one of
`0`, `1`, `2`, and so on. This shouldn't be surprising as that's what our phone
number specification dictates. The crucial thing is what is missing. Namely,
there are no `:.:` or `:|:` constructors used to represent sequencing and
alternatives. These are gone now and so is the need to branch on them. So the
unoptimised staged regex compiler does better than the interpreter because it
does less work.

The same splice also reveals the answer to the next question. Optimisations do
well on this expression because there is a larger surface area to optimise.
Staging generated one big state machine where most information is available such
as the branching structure and the concrete arguments of combinators. This is
not the case for the interepreter and the optimiser is restricted to work on
what is in each branch for the regex constructors.

To confirm this, we compare intermediate representation (Core) dumps of Haskell
with and without optimisations. To do so, we pass the `-O0` or `-O1`,
`-ddump-simpl`, and `-ddump-to-file` GHC options which generate a
`Foo.dump-simpl` file with a Core output after optimisations are applied at the
desired optimisation level. At the top of these files, there some basic
statistics, comparing these alone tells a story.

```
-O0:
  Result size of Tidy Core
    = {terms: 2,432, types: 4,705, coercions: 0, joins: 0/0}
-O1
  Result size of Tidy Core
    = {terms: 1,623, types: 1,069, coercions: 0, joins: 70/70}:
```

The first difference is the significant decline in the number of terms and
types. This is not surprising when we look at the core output. While the
unoptimised code is full of calls to functorial, applicative, and monadic
operators we used to implement regular expressions, the optimised version
doesn't have any. These could be eliminated because their arguments became known
with staging.

Here are representative excerpts from the core files. Don't focus too much on
what they do, but just observe the lack of combinators in the optimised version.

Unoptimised core:
```haskell
compiledPhoneNumber =
Control.Monad.>=> @ Maybe @ String @ [Char] @ String
  GHC.Base.$fMonadMaybe
  -- ***Omitted 10 nested calls to of monadic/applicative combinators***
  (Control.Monad.>=> @ Maybe @ String @ [Char] @ [Char]
     GHC.Base.$fMonadMaybe
     (<*> @ ((->) [Char]) (GHC.Base.$fApplicative-> @ [Char]) @ (Maybe [Char])
        @ (Maybe [Char])
        (<$> @ ((->) [Char]) @ (Maybe [Char]) @ (Maybe [Char] -> Maybe [Char])
           (GHC.Base.$fFunctor-> @ [Char])
           (GHC.Base.<|>
              @ Maybe GHC.Base.$fAlternativeMaybe @ [Char])
           (\ (ds_d62q :: [Char]) ->
              case ds_d62q of {
                [] -> GHC.Maybe.Nothing @ [Char];
                : c'_a5jT rest_a5jU ->
                  case ==
                         @ Char
                         ghc-prim-0.6.1:GHC.Classes.$fEqChar
                         (ghc-prim-0.6.1:GHC.Types.C# '0'#)
                         c'_a5jT
                  of {
                    False -> GHC.Maybe.Nothing @ [Char];
                    True -> GHC.Maybe.Just @ [Char] rest_a5jU
                  }
              }))
        (pure @ Maybe GHC.Base.$fApplicativeMaybe @ [Char]))
     (<*> @ ((->) [Char])
        (GHC.Base.$fApplicative-> @ [Char]) @ (Maybe [Char]) @ (Maybe [Char])
        (<$> @ ((->) [Char]) @ (Maybe [Char]) @ (Maybe [Char] -> Maybe [Char])
           (GHC.Base.$fFunctor-> @ [Char])
           (GHC.Base.<|>
              @ Maybe GHC.Base.$fAlternativeMaybe @ [Char])
           (\ (ds_d62t :: [Char]) ->
              case ds_d62t of {
                [] -> GHC.Maybe.Nothing @ [Char];
                : c'_a5jV rest_a5jW -> ...
```

Optimised core:
```haskell
StagedPhoneNumber.compiledPhoneNumber2 =
\ (x_X5SR [OS=OneShot] :: [Char]) ->
join {
  $w$j_sa1I [InlPrag=NOUSERINLINE[2], Dmd=<L,1*C1(U)>]
    :: ghc-prim-0.6.1:GHC.Prim.Void# -> Maybe String
  [LclId[JoinId(1)], Arity=1, Str=<L,A>, Unf=OtherCon []]
  $w$j_sa1I _ [Occ=Dead, OS=OneShot]
  -- Omitted 5 levels of nested joins
  = join {
      $w$j6_sa1w [InlPrag=NOUSERINLINE[2], Dmd=<L,1*C1(U)>]
        :: ghc-prim-0.6.1:GHC.Prim.Void# -> Maybe String
      [LclId[JoinId(1)], Arity=1, Str=<L,A>, Unf=OtherCon []]
      $w$j6_sa1w _ [Occ=Dead, OS=OneShot]
        = case x_X5SR of {
            [] -> GHC.Maybe.Nothing @ String;
            : c'_a886 rest_a887 ->
              case c'_a886 of
              { ghc-prim-0.6.1:GHC.Types.C# y_a5S2 ->
              case y_a5S2 of {
                __DEFAULT -> GHC.Maybe.Nothing @ String;
                '7'# ->
                  StagedPhoneNumber.compiledPhoneNumber3
                    rest_a887;
                '8'# ->
                  StagedPhoneNumber.compiledPhoneNumber3
                    rest_a887;
                '9'# ->
                  StagedPhoneNumber.compiledPhoneNumber3
                    rest_a887
              }
              }
  ...
```

The second thing to observe the proliferation of joins. These are both present
above in the optimised core output and also in the summary. The unoptimised core
had no joins, but the optimised version has 70. What are these joins? They are
evidence of _commuting conversion_ optimisation taking place. Given a nested
conditional, this conversion brings the inner conditional with the outer one,
e.g.,

```haskell
if (if e1 then e2 else e3) then e4 else e5
```
becomes
```haskell
if e1 then (if e2 then e4 else e5) else (if e3 then e4 else e5)
```

This conversion can trivialise some conditionals to the extent that we can
delete them.

The following nested case expressions for testing an empty list
```haskell
case (case as of { [] -> Nothing; (p:_) -> Just p }) of
  Nothing -> True
  Just _  -> False
```
becomes
```haskell
case as of
  []  -> case Nothing of Nothing -> True
                        Just z  -> False
  p:_ -> case Just p of Nothing -> True
                        Just _ -> False
```
which in turn simplifies to
```haskell
case as of
  []  -> True
  p:_ -> False
```

Join points in GHC are used to mitigate the effects of duplication of
expressions due to commuting conversion. You can learn more about them and
commuting conversion in [Join Points in
GHC](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/join-points-pldi17.pdf)
(Maurer et al. 2017).

The abundance of joins in the optimised Core program combined with the nested
case expressions due to staging make it likely that commuting conversion is a
significant factor in why optimisations are effective on our staged code. At
least, that is my educated guess.

## Qualitative remarks on ergonomics

### Staging might require restructuring

Whether the staging is as simple as placing quotations and splices depends on
the structure of the implementation. Consider the following implementation
without using any combinators:

```haskell
interpret :: RegExp -> Matcher
interpret Null cs = Just cs
interpret (Char c) cs =
  case cs of
    (c' : rest) | c == c' -> Just rest
    _ -> Nothing
interpret (re1 :|: re2) cs =
  case interpret re1 cs of
    Just cs' -> Just cs'
    Nothing -> interpret re2 cs
interpret (re1 :.: re2) cs =
  case interpret re1 cs of
    Just cs' -> interpret re2 cs'
    Nothing -> Nothing
interpret (Star re) cs = matchStar (interpret re) cs
```

This implementation is not amenable to staging only by placing quotations and
splices. We need to move `cs` over to the right side of the equations because
unlike `Matcher`, `Code Matcher` is not a function type. Once that is done, we
can mechanically place quotations and splices as before.

```haskell
compile :: RegExp -> Code Matcher
compile Null = [|| Just ||]
compile (Char c) =
  [||
    \case
      (c' : rest) | c == c' -> Just rest
      _ -> Nothing
  ||]
compile (re1 :|: re2) =
  [||
    \cs ->
      case $$(compile re1) cs of
        Just cs' -> Just cs'
        Nothing -> $$(compile re2) cs
  ||]
compile (re1 :.: re2) =
  [||
    \cs ->
      case $$(compile re1) cs of
        Just cs' -> $$(compile re2) cs'
        Nothing -> Nothing
  ||]
compile (Star re) = [|| matchStar $$(compile re) ||]
```

Although this is something to be aware, it is not a big price to pay.

### Aren't quotations and splices automatic?

Using `Code Matcher` instead of `Matcher` completely determines where the
splices and quotations need to be placed without any ambiguity or significant
modification to the code. This raises the question why do we need to do
something that requires no programmer ingenuity? Isn't it better to leave it to
the compiler to synthesise? I am not sure about the answer.

I know staged computation in [ML-like languages can be understood as the S4
temporal modal logic](https://www.cs.cmu.edu/~fp/papers/jacm00.pdf) (2000,
Davies and Pfenning). Quoting and splicing correspond to boxing and unboxing.
Further, I know that in some linear logics boxing and unboxing at term-level can
sometimes be synthesised. This makes me wonder if the same is possible for
staged computation. If so, it feels like a shame to do something mechanical by
hand.

### Polymorphism: have your interpreter and your compiler too!

Although we framed the staged interpreter as a more efficient version of the
original interpreter, staging can't help us if the regular expression isn't
known at compile time.

## Conclusion
