---
title: The Essence of Datalog
postType: Technical
inWhich: we implement a simple Datalog engine in not many lines of Haskell and
  discuss its semantics.
published: true
---

Datalog is arguably the simplest logic programming language there is. Depending
on your background, you can see it as a declarative SQL or a Prolog wih manners.
It has recently become popular among people who analyse programs at scale.
Semantically, it is simple and clean, so it doesn't take many lines of Haskell
to produce an (inefficient) implementation. Hopefully, this post should give you
some feel for logic programming and relational programming and also demonstrate
that λ-calculus is not the only language you can implement with ease in Haskell.

We start by explaining a simple program and then implement an evaluator for it.
Along with the implementation, we give a lightweight discussion of semantic
concerns, in particular about its termination. Later, we try quenching the
thirst for efficiency a little by giving some avenues for optimisation and
conclude with where to go next for those interested. There is a copy of the full
implementation at the end of the post.

## A crash course in logic programming

The litmus test for any logic programming language is to be able to compute a
variation of the following ancestry program.

```prolog
advisor("Andrew Rice",     "Mistral Contrastin").
advisor("Dominic Orchard", "Andrew Rice").
advisor("Andy Hopper",     "Andrew Rice").
advisor("Alan Mycroft",    "Dominic Orchard").
advisor("David Wheeler",   "Andy Hopper").
advisor("Rod Burstall",    "Alan Mycroft").
advisor("Robin Milner",    "Alan Mycroft").

academicAncestor(X,Y) :- advisor(X,Y).
academicAncestor(X,Z) :- advisor(X,Y), academicAncestor(Y,Z).
```

This particular variation has some facts about my academic geneology encoded in
the `advisor` relation and has some basic rules that defines what it means to
be an `academicAncestor`. The facts are no different than a database table. The
allow us to deduce new knowledge out using the facts. The first rule says that
an advisor is an ancestor. The second one says the advisor of a known ancestor
is an advisor.

The ability to use recursion to specify relationships in data was one of the
original selling points of Datalog.

We need to be able to query the data explicitly and implicitly represented in
this program. Here are some example queries:

```prolog
?- academicAncestor("Robin Milner", Intermediate),
   academicAncestor(Intermediate, "Mistral Contrastin").
?- academicAncestor("Alan Turing", "Mistral Contrastin").
?- academicAncestor("David Wheeler", "Mistral Contrastin").
```

The first one says "is there an academic ancestarial connection between Robin
Milner and I and if so who?". The second one says "is Alan Turing my academic
ancestor" and the third one is the same question but for David Wheeler.

Another appeal of Datalog can be seen in these queries. See how the first query
varies the binding in different uses of the same predicate. In Datalog,
everything is really just relations (hence the name relational programming).
This means there are no inherent inputs and outputs. You can leave a variable in
place of the knowledge you want to know and the system fills it for you. This
often means you can write a program for a particular input and output
relationship in mind and you get the opposite program for free.

## Evaluating a Datalog

Datalog is similar to λ-calculus in the sense that there are as many
variants of both as there are sands in a beach.[^extensions] The variation we
are going to implement today is the simplest one there is. The bits and pieces
you see in the previous section are all you get.

We'll implement the engine the way we evaluate Datalog programs: _initially, one
rule at a time, then all at once_. Since Datalog is deeply rooted in database
theory, it is usually implemented as relational algebra concepts such as joins
and selections. I have a programming language background, so I'll use
substitutions instead. They are entirely equivalent, but use of subsitutions
leads to simpler code.

### Representing Datalog

A rule consists of a head and a body. A head is an atom and so are the comma
separated items in the body. An atom then consists of a predicate name like
`advisor` and a list of terms. We have two kinds of terms: variables and
symbols. This corresponds to few simple datatype declarations.

```haskell
data Rule = Rule { _head :: Atom, _body :: [ Atom ] }
data Atom = Atom { _predSym :: String, _terms :: [ Term ] } deriving Eq
data Term = Var String | Sym String deriving Eq
```

The following rule

```prolog
academicAncestor(X,Z) :- advisor(X,Y), academicAncestor(Y,Z).
```

corresponds to

```haskell
Rule (Atom "academicAncestor" [ Var "X", Var "Z" ])
  [ Atom "advisor"          [ Var "X", Var "Y" ]
  , Atom "academicAncestor" [ Var "Y", Var "Z" ] ]
```

Facts are just bodiless rules. For example,

```prolog
advisor("Andrew Rice", "Mistral Contrastin").
```

corresponds to

```haskell
Rule (Atom "advisor" [ Sym "Andrew Rice", Sym "Mistral Contrastin" ]) []
```

You might be thinking but what about the queries, the Rule datatype doesn't
allow headless bodies. That's true but the dirty secret about queries is that
they get rewritten as rules with the head atom generated from the query. The
predicate symbol for each query is fresh and the terms of the head are just the
variables in the body. For example,

```prolog
?- academicAncestor("Robin Milner", Intermediate),
   academicAncestor(Intermediate, "Mistral Contrastin").
```

gets fresh head atom `query1(Intermediate)` and can be thought of as

```prolog
query1(Intermediate) :-
  academicAncestor("Robin Milner", Intermediate),
  academicAncestor(Intermediate, "Mistral Contrastin").
```

An entire Datalog program is nothing but a collection of rules.

```haskell
type Program = [ Rule ]
```

We also need a way of representing the known facts about the universe. We can
call this our _knowledge base_. For simplicity, we use a horribly inefficient
list of atoms.

```haskell
type KnowledgeBase = [ Atom ]
```

Since we'll use substitutions to evaluate atoms, we can define that here too.

```haskell
type Substitution = [ (Term, Term) ]
```

Our substitutions are simpler than those that are used in λ-calculus. A Haskell
tuple `(x,c)` represents the substituion `[c/x]`. Here, `x` is always a variable
and `c` is always a constant (symbol). The variable restriction is usual; it is
just not reflected in the type. The constant restriction, however, is not.
Datalog doesn't have function symbols and as we'll see substituting a variable
is anywhere in the evaluation. Like the variable restriction, the constant
restriction is also not reflected in the type.

We can also define the only constant that will be used in the evaluator: the
empty substitution.

```haskell
emptySubstitution :: Substitution
emptySubstitution = []
```

Mind-blowing, I know.

### One rule at a time

Let's focus on evaluating a single rule from our example program.

```prolog
academicAncestor(X,Z) :- advisor(X,Y), academicAncestor(Y,Z).
```

We know some facts about the world and using this rule, we want to know some
more. There are two ways. One is to gather everything we know about
`advisor` and `academicAncestor` separately and _join_ them together making
sure the second parameter of `advisor` (`Y`) matches the first parameter of
`academicAncestor` (`Y`). Another way is to look at any one of the atoms and
find assignments to its variables and substitute them in the other atom, only
then we look for assignments to the remaining variables of this second atom.
This approach would work for the example above as follows: find possible
assignments to `X` and `Y` through `advisor`, substitute the values of `Y` in
`academicAncestor`, and finally look for values of `academicAncestor` in the
knowledge base that agree on the newly substituted value of `Y` to obtain values
for `Z`.

In database context, the first is called _join before select_ and the second is,
not so surprisingly, _select before join_.  We'll implement the latter because
it makes the code simpler.[^select-before-join]

Since we need unification to obtain substitutions from facts & body atoms and
substitution to ground further atoms. We start by implementing those.

```haskell
substitute :: Atom -> Substitution -> Atom
substitute atom substitution = atom { _terms = map go (_terms atom) }
  where
  go sym@Sym{} = sym
  go var@Var{} = fromMaybe var (var `lookup` substitution)
```

Substitution is pretty much what you would expect looking up what to substitute
for variables and do it whenever it can find a binding otherwise leaving the
variable alone.

```haskell
unify :: Atom -> Atom -> Maybe Substitution
unify (Atom predSym ts) (Atom predSym' ts')
  | predSym == predSym' = go $ zip ts ts'
  | otherwise           = Nothing
  where
  go :: [ (Term, Term) ] -> Maybe Substitution
  go []                           = Just emptySubstitution
  go ((s@Sym{}, s'@Sym{}) : rest) = if s == s' then go rest else Nothing
  go ((v@Var{}, s@Sym{})  : rest) = do
    incompleteSubstitution <- go rest
    case v `lookup` incompleteSubstitution of
      Just s' | s /= s'   -> Nothing
      _                   -> return $ (v,s) : incompleteSubstitution
  go ((_, Var{}) : _) = error "The second atom is assumed to be ground."
```

Unification is also simple, in fact, too simple. For one thing, we cheat and
unify whenever we have two atoms that have the same predicate symbol. In
Datalog, a predicate is determined by its predicate symbol _and_ arity
(the number of terms). Here, we assume each predicate symbol determines
the arity. More importantly, we throw an error when the second argument atom is
a variable. The reason is unification only occurs between a body atom and an
atom that appears as a fact. Since facts cannot have variables, this is safe.
This is consistent with our earlier assumptions about the form of substitutions.

We take special care of unification of atoms with repeated variables. It
requires failing in case of a contradictory variable assignment.  Consider
unifying `p(X,X)` with `p("a","b")`.

Next we evaluate an atom into a list of substitutions by finding facts that fit
the template provided by a body attom and capturing the assignments to its
variables. Those assignments to variables are just the substitutions we are
looking for.

```haskell
evalAtom :: KnowledgeBase -> Atom -> [ Substitution ] -> [ Substitution ]
evalAtom kb atom substitutions = do
  substitution <- substitutions
  let downToEarthAtom = substitute atom substitution
  extension <- mapMaybe (unify downToEarthAtom) kb
  return $ substitution <> extension
```

Here we do exactly what is described above but build the substitutions by
accumulation. This means we have substitutions that we use on the body atom to
ground its variables, but then unifying this more down to earth atom (it's more
ground, get it?) with the facts we know gives us extensions to the substitution
we start with. Thus, we extend and accumulate substitutions.

Now all we need to do is to walk the body and accumulate substitutions, then
using these substitutions we deduce new facts based on the head of the rule.

```haskell
walk :: KnowledgeBase -> [ Atom ] -> [ Substitution ]
walk kb = foldr (evalAtom kb) [ emptySubstitution ]

evalRule :: KnowledgeBase -> Rule -> KnowledgeBase
evalRule kb (Rule head body) = map (substitute head) (walk kb body)
```

Here's something to think about. We said the facts we deduce will be ground, but
`evalRule` does not check if the substitution has a binding for all the
variables that appear in the head. Does that mean we are potentially concluding
non-ground facts? Don't worry if you're not sure, we'll come back to it
[below](#range-restriction).

### All at once

All we need now is to evaluate all of the rules together. We'll do one of the
simplest possible things. We'll evaluate each rule independently and then
concatenate the newly derived facts together and bundle them with what we
already know. Then repeat the process until we can't produce new facts any more.

```haskell
immediateConsequence :: Program -> KnowledgeBase -> KnowledgeBase
immediateConsequence rules kb =
  nub . (kb <>) . concatMap (evalRule kb) $ rules

solve :: Program -> KnowledgeBase
solve rules =
  if all isRangeRestricted rules
    then fix step []
    else error "The input program is not range-restricted."
  where
  step :: (KnowledgeBase -> KnowledgeBase) -> (KnowledgeBase -> KnowledgeBase)
  step f currentKB | nextKB <- immediateConsequence rules currentKB =
    if nextKB == currentKB
      then currentKB
      else f nextKB
```

The `immediateConsequence` function does the bundling step and `solve` computes
the fixpoint from an empty set of facts.

The only thing left unexplained is the `isRangeRestricted` predicate which
ensures the program is well-formed and is explained next.

### Correctness, termination, and testing

Now that we have something that almost compiles we can talk about correctness.
Starting with the last missing piece: the range restriction predicate.

#### Range restriction

In a rule, if every variable in the head appears somewhere in the body, we call
the rule range-restricted. We check if the program is range-restricted before
evaluating it with `solve`.[^dependent-range-restriction] This is why while
evaluating a rule (using `evalRule`), we didn't have to check if there are any
variables left in the head after substitution.

```haskell
isRangeRestricted :: Rule -> Bool
isRangeRestricted Rule{..} =
  vars _head `isSubsequenceOf` concatMap vars _body
  where
  vars Atom{..} = nub $ filter (\case {Var{} -> True; _ -> False}) _terms
```

There still remains the question of why we need range restriction at all?  After
all, the ability to deduce generic facts seems useful. For example, stating
`p(X,X)` as a fact is a compact way of saying `p` is reflexive.

The problem is something called _domain independence_. It basically means if
the set of values a variable can take changes from one database to another (but
not the instances itself), the query should still compute the same thing. In
other words, it prevents your program's result to change under your feet if the
values in your database are the same. Since checking domain independence in
general is undecidable, we use range restriction as a safe syntactic
approximation achieves domain independence.

So in this implementation what this means is if I change the definition of
datatype `Term` such that the symbols do not use `String` but instead a type for
strings up to length 10, if my initial ground facts were all strings of length
up to 10, then the results to all queries remain the same. We can't guarantee
the same thing if there is domain dependence.

Another problem is that when a query is posed with free variables, we expect
values to be filled for that variable. If we can deduce a generic fact such as
`p(X,X)`, then asking for what values `X` might have well be the set of infinite
strings.

Bear in mind, there are Datalog's that lifts this restriction and it is not too
much work. We just need a notion of α-equivalence, a store that can handle
non-ground values, and a unification algorithm that handles variables.

#### Does the immediate consequence function have redundancy?

Prepending already known facts may look redundant at first since our
implementation is so inefficient that it will rederive all the known facts in
each iteration. You are right, but it allows us to use list equality in place of
set equality as the termination condition which we dive more into next.

#### Every good thing must come to an end

Does this procedure terminate? Yes, it does. When? So long as you don't have
infinite programs. It would be a cheeky thing to do though. One of the appeals
of Datalog is that it is not Turing-complete and every query to the system
terminates.

The termination argument is pretty simple. Immediate consequence function is
_monotone_ that is the facts it produces encompasses the facts it starts with.
Further, the number of facts that can be produced is _bounded_ if we start with
a finite database. Our initial set of facts used to kickstart `solve` is empty.
Hence, as long as our program is finite, we have finite number of
facts.[^infinite-programs] As an upper bound, if we have $N$ constants
throughout the program, then for each relation $r$ of arity $k$, we can have at
most $N^k$ facts. So the number of facts we can produce is also finite.

One place I'm being a bit loose is the monotone bit. What I said makes sense
with sets, but we're working here with lists. Although `[1,2,3]` and `[2,1,3]`
encompass each other, they don't compare equal using `==`. The reason this
implementation never gets in a cycle is because `nub` function called on the
amalgemation of facts in `immediateConsequence` preserves the first occurrence
of each element in the list and since we prepend the already known facts before
calling `nub`, `==` behaves as if it is set equality.

If you want to sound smart explaining all of this and reduce the size of your
audience to a group of people who would understand this without you mentionning
anyway, you can just say the following. We have a non-empty finite lattice which
means it is complete and [Knaster-Tarski
theorem](https://en.wikipedia.org/wiki/Knaster–Tarski_theorem) (which is a very
cool theorem ❤️) applied to the immediate consequence monotone function over this
complete lattice implies that it has a least fixpoint.

#### Quality assurance

Time for the litmus test. We can now translate the ancestory program from
earlier into Haskell.

```haskell
ancestor :: Program
ancestor =
  -- Facts
  fmap (\terms -> Rule (Atom "advisor" terms) [])
    [ [ Sym "Andrew Rice",     Sym "Mistral Contrastin" ]
    , [ Sym "Dominic Orchard", Sym "Mistral Contrastin" ]
    , [ Sym "Andy Hopper",     Sym "Andrew Rice" ]
    , [ Sym "Alan Mycroft",    Sym "Dominic Orchard" ]
    , [ Sym "David Wheeler",   Sym "Andy Hopper" ]
    , [ Sym "Rod Burstall",    Sym "Alan Mycroft" ]
    , [ Sym "Robin Milner",    Sym "Alan Mycroft" ]
    ] <>
  -- Actual rules
  [ Rule (Atom "academicAncestor" [ Var "X", Var "Y" ])
      [ Atom "advisor" [ Var "X", Var "Y" ] ]
  , Rule (Atom "academicAncestor" [ Var "X", Var "Z" ])
      [ Atom "advisor"          [ Var "X", Var "Y" ]
      , Atom "academicAncestor" [ Var "Y", Var "Z" ] ]
  ] <>
  -- Queries
  [ Rule (Atom "query1" [ Var "Intermediate" ])
      (fmap (Atom "academicAncestor")
        [ [ Sym "Robin Milner", Var "Intermediate" ]
        , [ Var "Intermediate", Sym "Mistral Contrastin" ] ])
  , Rule (Atom "query2" [ ])
      [ Atom "academicAncestor"
          [ Sym "Alan Turing", Sym "Mistral Contrastin" ] ]
  , Rule (Atom "query3" [ ])
      [ Atom "academicAncestor"
          [ Sym "David Wheeler", Sym "Mistral Contrastin" ] ]
  ]
```

We can make querying a bit more pleasant with a function that returns possible
bindings.

```haskell
query :: String -> Program -> [ Substitution ]
query predSym pr =
  case queryVarsL of
    [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms
    [] -> error $ "The query '" ++ predSym ++ "' doesn't exist."
    _  -> error $ "The query '" ++ predSym ++ "' has multiple clauses."
  where
  relevantKnowledgeBase = filter ((== predSym) . _predSym) $ solve pr
  relevantKnowledgeBaseSyms = _terms <$> relevantKnowledgeBase

  queryRules = filter ((== predSym) . _predSym . _head) pr
  queryVarsL = _terms . _head <$> queryRules
```

All it does it to run the program, find the named query and return the bindings
to its arguments. Let's execute all three queries.

```
> query "query1" ancestor
[[(Intermediate,"Dominic Orchard")],[(Intermediate,"Alan Mycroft")]]
> query "query2" ancestor
[]
> query "query3" ancestor
[[]]
```

All three queries return the expected results. Dominic Orchard and Alan Mycroft
are between me and Robin Milner. I am not an academic descendant of Alan Turing,
but I am of David Wheeler.

Since these three queries run fine, we can safely conclude that the evaluator
here is bug-free.

## Addressing the turtle in the room

As I mentioned before, this evaluator is inefficient. Discussing the reasons why
and what we can do to make it better is not only a software engineering
exercise, but also another way of highlighting why Datalog is a good language.

### Optimise for the query

Basically, all I told you about Datalog semantics is incomplete. You'll struggle
to find a resource that discusses Datalog evaluation the way I do because the
semantics are always defined with respect to a query. So what we really need is
a program query pair. What we compute here is much stronger and also
unnecessary. For example, if the queries we are interested in only involved the
`advisor` relation, computing `academicAncestors` would be a waste of time.

One way of dealing with this is to use a top-down evaluator which starts from
the query and uses something called _resolution_ which is a proof technique.
This allows (pretty easily) only the relevant facts to be derived along the way.
Most Prolog interpreters use a similar top-down evaluation strategy. It is not
preferred in Datalog for various reasons. One of which is that the naïve
implementation allows infinite loops.

We can achieve in a bottom-up evaluator (like ours) the same thing using _magic
set transformation_. The very long story short, based on the input program, it
generates magic rules based on the dataflow of the program and inserts atoms
defined by these rules into the original rule bodies to restrict what can be
derived.  Its effectiveness varies from program to program and there are
alternatives to it. If you want to learn more about it, you can look at [On the
Power of
Magic](https://www.sciencedirect.com/science/article/pii/074310669190038Q) by
Beeri and Ramakrishnan which you must admit is the best name for an academic
paper.

### Semi-naïve evaluation

While discussing [range restriction](#range-restriction), we mentioned that
this implementation rederives all the known facts in each iteration. This is
awful and is why it is called the naïve evaluation. There is also a modestly
named semi-naïve evaluation. It exploits a simple observation. In order to
derive a new fact from a rule, at least one new fact of the previous iteration
needs to be used.

The way this gets implemented is that we maintain a delta of facts and as well
as an accumulator and rewrite the rules to make versions of them that uses the
deltas.

This is particularly effective for the so called _linear rules_ such as the
recursive `academicAncestor` rule which only has one derived predicate in its
body. In that case, the semi-naïve evaluation turns a quadratic evaluation into
a linear one.

### Incremental evaluation

Datalog is amenable to incremental evaluation. Even in this version of the
evaluator, you can see that when a fixpoint is reached, we can enrich the
resulting knowledge base with additional facts and apply the fixpoint algorithm
again. This performs at least as good as starting from scratch and often much
much better.

The situation gets more complicated when there is negation in the language
because additional facts invalidate facts that depend on the negation of those
facts. This is a particular instance of [_non-monotonic
reasoning_](https://en.wikipedia.org/wiki/Non-monotonic_logic). However,
Datalog, overall, is still a good language if you're after incremental
evaluation.

Furthermore, the idea of incremental evaluation is intricately connected with
maintaining a delta of facts. If your evaluator uses semi-naïve evaluation
already, having an incremental evaluator is not much extra effort.

### Data structures

Using lists to compute over sets is a bad idea. Depending on the application,
hash tables, proper databases, in memory key-value stores, or at the very least
of `Set` and `Map` modules from the `containers` package will certainly make
things better. Use of sets in general is a good idea because then we don't have
to rely on `nub` function's internals for termination as discussed
[earlier](#every-good-thing-must-come-to-an-end).

### Dependency graphs

We evaluate all rules in one pot but that is also very inefficient. We can
partition the program by determening dependencies between predicates. Then we
compute the fixpoint of the rules with no unevaluated dependencies. This allows
us to consider fewer rules that already have reached their fixpoints.

For example, in the ancestor program we would have a graph with `ancestor` and
`academicAncestor` notes where the former points to the latter and the latter
loops around. Meaning we can compute the fixpoint for `ancestor` rules first,
then forget about those rules and compute the ones for `academicAncestor`.

Also if your Datalog variant has _stratified negation_ which is a popular way of
incorprating negatom atoms, you already have to do the dependency analysis and
partition your program. So engineering-wise, this optimisation comes for free.

### Paralellisation

Datalog evaluation is great for data-paralel computation. Even in our
implementation, evaluating all the rules in a given iteration is an
embarassingly parallel problem. The dependency graph can be used to further
paralellise the evaluation using work queues.

## Closing remarks

Short program, long prose is the theme. I hope I managed to give some idea about
how a simple Datalog variant works. I tried to squeeze in as much semantics and
tips for more efficient implementation as possible which is probably more useful
than a short program.

If you want to look at Datalog further.
[Souffle](https://souffle-lang.github.io) is a modern variant geared towards
program analysis and is blazingly fast.

If you are interested in a more formal treatment of Datalog as well as some of
the optimisations I mentioned chapters 12 to 15 of [Foundations of
Databases](http://webdam.inria.fr/Alice/) by Abiteboul, Hull, and Vianu are
probably the best resources which collect everything together in such detail and
with modern exposition.

## Full program

Here's the full program for your convenience.

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module SimpleDatalog where

import Data.Function (fix)
import Data.List (nub, intercalate, isSubsequenceOf)
import Data.Maybe (mapMaybe, fromMaybe, isNothing)

type Program = [ Rule ]

data Rule = Rule { _head :: Atom, _body :: [ Atom ] }

data Atom = Atom { _predSym :: String, _terms :: [ Term ] } deriving Eq

data Term = Var String | Sym String deriving Eq

type KnowledgeBase = [ Atom ]

type Substitution = [ (Term, Term) ]

emptySubstitution :: Substitution
emptySubstitution = []

solve :: Program -> KnowledgeBase
solve rules =
  if all isRangeRestricted rules
    then fix step []
    else error "The input program is not range-restricted."
  where
  step :: (KnowledgeBase -> KnowledgeBase) -> (KnowledgeBase -> KnowledgeBase)
  step f currentKB | nextKB <- immediateConsequence rules currentKB =
    if nextKB == currentKB
      then currentKB
      else f nextKB

isRangeRestricted :: Rule -> Bool
isRangeRestricted Rule{..} =
  vars _head `isSubsequenceOf` concatMap vars _body
  where
  vars Atom{..} = nub . filter (\case { Var{} -> True; _ -> False }) $ _terms

immediateConsequence :: Program -> KnowledgeBase -> KnowledgeBase
immediateConsequence rules kb =
  nub . (kb <>) . concatMap (evalRule kb) $ rules

evalRule :: KnowledgeBase -> Rule -> KnowledgeBase
evalRule kb (Rule head body) = map (substitute head) (walk kb body)

walk :: KnowledgeBase -> [ Atom ] -> [ Substitution ]
walk kb = foldr (evalAtom kb) [ emptySubstitution ]

evalAtom :: KnowledgeBase -> Atom -> [ Substitution ] -> [ Substitution ]
evalAtom kb atom substitutions = do
  substitution <- substitutions
  let downToEarthAtom = substitute atom substitution
  extension <- mapMaybe (unify downToEarthAtom) kb
  return $ substitution <> extension

substitute :: Atom -> Substitution -> Atom
substitute atom substitution = atom { _terms = map go (_terms atom) }
  where
  go sym@Sym{} = sym
  go var@Var{} = fromMaybe var (var `lookup` substitution)

unify :: Atom -> Atom -> Maybe Substitution
unify (Atom predSym ts) (Atom predSym' ts')
  | predSym == predSym' = go $ zip ts ts'
  | otherwise           = Nothing
  where
  go :: [ (Term, Term) ] -> Maybe Substitution
  go []                           = Just emptySubstitution
  go ((s@Sym{}, s'@Sym{}) : rest) = if s == s' then go rest else Nothing
  go ((v@Var{}, s@Sym{})  : rest) = do
    incompleteSubstitution <- go rest
    case v `lookup` incompleteSubstitution of
      Just s' | s /= s'   -> Nothing
      _                   -> return $ (v,s) : incompleteSubstitution
  go ((_, Var{}) : _) = error "The second atom is assumed to be ground."

{-
- advisor("Andrew Rice",     "Mistral Contrastin").
- advisor("Dominic Orchard", "Andrew Rice").
- advisor("Andy Hopper",     "Andrew Rice").
- advisor("Alan Mycroft",    "Dominic Orchard").
- advisor("David Wheeler",   "Andy Hopper").
- advisor("Rod Burstall",    "Alan Mycroft").
- advisor("Robin Milner",    "Alan Mycroft").
-
- academicAncestor(X,Y) :- advisor(X,Y).
- academicAncestor(X,Z) :- advisor(X,Y), academicAncestor(Y,Z).
-
- ?- academicAncestor("Robin Milner", Intermediate),
-    academicAncestor(Intermediate, "Mistral Contrastin").
- ?- academicAncestor("Alan Turing", "Mistral Contrastin").
- ?- academicAncestor("David Wheeler", "Mistral Contrastin").
-}
ancestor :: Program
ancestor =
  -- Facts
  fmap (\terms -> Rule (Atom "advisor" terms) [])
    [ [ Sym "Andrew Rice",     Sym "Mistral Contrastin" ]
    , [ Sym "Dominic Orchard", Sym "Mistral Contrastin" ]
    , [ Sym "Andy Hopper",     Sym "Andrew Rice" ]
    , [ Sym "Alan Mycroft",    Sym "Dominic Orchard" ]
    , [ Sym "David Wheeler",   Sym "Andy Hopper" ]
    , [ Sym "Rod Burstall",    Sym "Alan Mycroft" ]
    , [ Sym "Robin Milner",    Sym "Alan Mycroft" ]
    ] <>
  -- Actual rules
  [ Rule (Atom "academicAncestor" [ Var "X", Var "Y" ])
      [ Atom "advisor" [ Var "X", Var "Y" ] ]
  , Rule (Atom "academicAncestor" [ Var "X", Var "Z" ])
      [ Atom "advisor"          [ Var "X", Var "Y" ]
      , Atom "academicAncestor" [ Var "Y", Var "Z" ] ]
  ] <>
  -- Queries
  [ Rule (Atom "query1" [ Var "Intermediate" ])
      (fmap (Atom "academicAncestor")
        [ [ Sym "Robin Milner", Var "Intermediate" ]
        , [ Var "Intermediate", Sym "Mistral Contrastin" ] ])
  , Rule (Atom "query2" [ ])
      [ Atom "academicAncestor"
          [ Sym "Alan Turing", Sym "Mistral Contrastin" ] ]
  , Rule (Atom "query3" [ ])
      [ Atom "academicAncestor"
          [ Sym "David Wheeler", Sym "Mistral Contrastin" ] ]
  ]

query :: String -> Program -> [ Substitution ]
query predSym pr =
  case queryVarsL of
    [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms
    [] -> error $ "The query '" ++ predSym ++ "' doesn't exist."
    _  -> error $ "The query '" ++ predSym ++ "' has multiple clauses."
  where
  relevantKnowledgeBase = filter ((== predSym) . _predSym) $ solve pr
  relevantKnowledgeBaseSyms = _terms <$> relevantKnowledgeBase

  queryRules = filter ((== predSym) . _predSym . _head) pr
  queryVarsL = _terms . _head <$> queryRules
```

[^extensions]: My impression is, as time goes on, λ-calculus variants try to
tame λ-calculus (simply typed, linear, dependent, etc.) while Datalog variants
(relaxed range-restriction, functional symbols, explicit quantification, etc.)
lets it run wild.

[^select-before-join]: As it happens, select before join is usually (but
certainly not always) the faster approach in real world. However, this doesn't
affect us at all because the performance benefit requires an indexed database
for the columns that are grounded by substitution.

[^infinite-programs]: Infinite programs are an interesting concept. I can't
think of any use for it though. Also evaluating them is tricky as you can't
traverse all your program statements, rules, etc. Notice that our Datalog
evaluator wouldn't be terminating not only because of a potential infinite facts
problem, but because we try to evaluate each rule.

[^dependent-range-restriction]: This is a simple check, but if we wanted, we
could make it even neater. Range-restriction is something that can be baked into
the `Rule` datatype using some dependent types. We would need to modify `Atom`
to keep track of its variables, but it is doable.  While at it we could also
make substitutions keep track of their variables, which would enable us to
enforce the assumptions about our substitutions. You see, this is my favourite
kind of dependent types. It doesn't give you full correctness, but eliminates a
whole class of software bugs and potentially give you some performance boost.
This may very well become a future blog post (famous last words on the topic).
