---
title: Staged Wins
postType: Technical
inWhich: we look at how effortless and profitable staged programming is in
  Haskell by microbenchmarking a regular expression interpreter and staged
  compiler.
published: false
lastUpdated: 2020-09-01
---

As Haskell programmers, we live and die by the maxim "never do at runtime what
could be done at compile time". However, we (or at least me) almost exclusively
understand this as doing safety checks before runtime and do not appreciate the
full generality of the maxim. Although an optimising compiler will do much
computation before runtime, as a programmer we hardly ever have a say on the
matter.

The singular exception to this in many languages compiled or otherwise is
_metaprogramming_ where the purpose of our code is to generate code. If you
think about it, the concept is remarkably prevalent in many languages from C
preprocessor macros to abuses of C++ template system, from Ruby's highly
maleable object model to Java's class loader API. In fact, in Haskell alone it
comes at least in three flavours: datatype-generic programming, Template
Haskell (henceforth TH), Typed-Template Haskell (henceforth TTH). The first is
convenient but comes at a runtime cost. The second one is performed at compile
time, but is unprincipled, potentially unhygienic, and effectively untyped. The
third restricts Template Haskell, but it achieves principled and well-typed
metaprograms with decent error messages!

TTH is thus what I discuss in this post. In particular, I take a naïve regular
expression recogniser and mindlessly apply TTH's quotations and splices to
answer two questions:

  1. Is it a pain to do use TTH?
  2. What do I get out of going through this exercise?

The short answers are "not really" and "4x performance improvement in time".
However, the justification for the first answer is my highly subjective value
judgements with caveats and that for the second is microbenchmarks on a few
examples. So if your reputation is on the line, I suggest you don't cite this
blog post to support your argument. For that, I'd go read articles, posts, and
libraries by [Matthew Pickering](https://mpickering.github.io), [Jeremy
Yallop](https://www.cl.cam.ac.uk/~jdy22/), or [Nada
Amin](https://namin.seas.harvard.edu/people/nada-amin).

In the rest of this post, we first quickly look at the regular expression
recogniser in question. We then stage it. Having two these interpreted and
staged versions at hand, we qualitatively compare them using microbenchmarks and
look at the generated code to try to understand the performance difference.
Finally, we remark on the convenience of staging this program and conclude.

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
words, the former produces the code for some evaluation and the latter *in the
right context* evaluates that code.

If you then have something you want evaluated at compile time for sure, you just
write a function of the form `a -> Code b`. The `a` is what you want to get rid
of at runtime and the `Code b` is what you end up with as a result.

In our case, we had an interpreter with type `RegExp -> Matcher` and we want to
compile the regular expression away, so we'd like a function `RegExp -> Code
Matcher` instead. Well, how are we going to get there? Mechanically! Mindlessly!
Mercilessly?

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

However, this won't compile because `compile` has type `RegExp -> Code Matcher`
then the expression inside the quotation needs to have the type `Matcher`. Thus,
the recursive calls are ill-typed. They have type `Code Matcher` instead of
`Matcher`, but we already know how to go in this direction with a splice!

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

The results indicate a convincing ~4x win when compiled with `-O0` and `-O2`
indicated by the microbenchmarks conducted using the `criterion` library.

![Microbenchmark results for -O0](/images/staged-wins/microbenchmarks-O0.png)

![Microbenchmark results for -O2](/images/staged-wins/microbenchmarks-O2.png)

### But why?

There are four reasons I can think of why staging would yield performance
benefits: domain-specific optimisations, enabling compiler optimisations,
microarchitectural wins, and doing less work.

We know it is not domain-specific optimisations because we haven't done any. By
comparing the graphs of -O0 and -O2, we can also see that the timings for
`compile` are consistent, so it is not GHC doing more optimisations (this
surprises me).

There remains the microarchitectural wins and doing less work. To see if these
are in play we need to take a deeper look.

## Qualitative remarks

## Conclusion
