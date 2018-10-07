---
title: Automatic Subgoal Scheduling for Datalog
postType: Technical
inWhich: we investigate dataflow in declarative programs and talk about how
  to make Datalog safer by statically reordering goals when predicates with
  dataflow constraints are involved.
---

I recently presented _"Automatic Reordering for Dataflow Safety of Datalog"_
(can be accessed freely if you follow the link from [my
homepage](https://dodisturb.me)) in the [20th Symposium on Principles and
Practice of Declarative
Languages](http://ppdp-lopstr-18.cs.uni-frankfurt.de/ppdp18.html). I
collabroated with [Dr Dominic
Orchard](https://www.cs.kent.ac.uk/people/staff/dao7/) and [Dr Andrew
Rice](https://www.cl.cam.ac.uk/~acr31/) for this work. A few commented that the
paper is technically dense and consequently hard going. I don't want this work
to be ignored because I suck at writing. So in an attempt to make things right
and also to do some PR, I will explain the major ideas of the paper without the
formalism and with numerous examples.

I want this post to be understandable with ease. If you find yourself confused
or bored at any point or found some terms that are not very well explained,
contact me via Twitter or email (both on [my homepage](https://dodisturb.me)).

After explaining some standard terminology about Datalog, we start by describing
what extralogical predicates are, why one might want them in Datalog, and what
problems they bring along. Then we clarify what is meant by invocation safety of
such predicates. This will lead us to the naïve, incomplete, and inefficient
solution and that will lead us to a better solution. I'll conclude by giving
summarising the main points, mentioning where this work work might go and why
you might like to look at the paper.

## Terminology

Let's briefly look at basic Datalog terminology through an example:

```prolog
ancestor(X,Z) :- parent(X,Y), parent(Y,Z).
```
```
                 -----------  -----------
                   Subgoal      Subgoal
-------------    ------------------------
    Head                   Body
------------------------------------------
                  Rule
```

 * This is a **rule** in Datalog (as it happens also in Prolog) with some parts
highlighted.
 * A rule consists of a **head** (to the left of `:-`{.prolog}) and a **body**
 (everything to the right of `:-`{.prolog}). A body is a comma separated list of
 **subgoals**.
 * A subgoal is a **predicate** applied to a tuple.
 * A **predicate** qualifies a tuple with a name (sort). Throughout the text, we
 write subgoals in `monospace` and predicates in $italic$. We sometimes say "the
 subgoal with $p$" to refer to a subgoal with the predicate $p$ inside.
 * A tuple of subgoal consists of **terms** which are either **constants** like
 `"Dragon Fruit"` (with quotation marks) or **variables** like `Fruit` (no
 quotations, always capitalised).

We're good to go! All other terms will be defined in the text as we go along.

## Motivation

#### Example 1

Here's a hypothethical Datalog rule that authenticates a user:

```prolog
auth(User,Pass) :- password(User,Pass), hash(Pass,Hash), valid(User,Hash).
```

The reading of any rule in Datalog is "if every subgoal in the body holds, then
we can conclude the head." In this specific case, we can authenticate a user if
we have a known password for a that user and the hash of that user is known to
be valid. One of the nicest parts of this reading is that it doesn't matter
which order the subgoals are presented, we still reach the same conclusion. For
example,
```prolog
auth(User,Pass) :- hash(Pass,Hash), password(User,Pass), valid(User,Hash).
```
would authenticate exactly the same users as the previous example.

When the predicates in a program are _logical_, there are no
dataflow restrictions for evaluation of a subgoal with that predicate. For
example, `password("Milner",Pass)`{.prolog} would bind the password of Milner to
`Pass` while `password(User,Pass)`{.prolog} would generate all known user and
password pairs. There are no inherent input and output parameters to a logical
predicate.

However, the $hash$ predicate stands out in the previous example because hash
functions (if they are any good) work only in one direction. It is unreasonable
to expect $hash$ to bind a value for the password given a hash. Let's refer to
predicates like $hash$ (those with dataflow requirements) as _extralogical_
predicates.

In light of this knowledge, the versions of the rule defining $auth$ above are
not equivalent. Evaluation of the subgoal `hash(Pass,Hash)`{.prolog} produces a
runtime error if the value of `Pass` is unknown. Suddenly, we have to be careful
about the way we order subgoals.  Not only those that are obviously extralogical
like $hash$, but also any user-defined predicates that make use of extralogical
ones! To make the matters worse, although semantically arithmetic
relations such as $>$ are logical, they are usually implemented as extralogical
predicates (or relations).

#### Example 2

Just when you think things are looking bleak, it gets worse. Extralogical
predicates may also cause code duplication. Let' look at another example:

```prolog
check_client(Pass) :- weak(Pass,Hash).
check_server(Hash) :- weak(Pass,Hash).

weak(Pass,Hash) :- hash(Pass,Hash), rainbow(Pass,Hash).
```

Here, we define a predicate $weak$ that checks if a password or a hash is weak.
It does so looking for the hash of the password in a rainbow function (a
function that can reverse _some_ hashes). Like $hash$, $rainbow$ is also
extralogical but in its second argument rather than the first. Now it is
beneficial for both the client and the server to check if a hash is weak, but
the client shouldn't know the hash of a given password (otherwise it can
construct a rainbow table of its own!) and the server shouldn't know the
password (in case it gets stolen). Hence, there are two predicates
$check_client$ that takes a password and $check_server$ that takes a hash that
can be used by the client and server respectively.

This example is worse than the previous one because regardless how careful the
programmer is, she can't rewrite the definition of $weak$ in a single rule such
that all dataflow requirements are satisfied. Now when $check_client$ is used,
$weak$ should have the subgoal `hash(Pass,Hash)`{.prolog} first, since the
password is known (satisfying $hash$'s dataflow requirement) and evalauting this
subgoal produces a hash, satisfying the dataflow requirement of $rainbow$.  If
$check_server$ is used, we need the opposite ordering because this time the hash
value is known initially. So neither rule alone can be used to satisfy the
requirements of the whole program. The only solution is a code duplicating
rewrite:
```prolog
check_client(Pass) :- weak_client(Pass,Hash).
check_server(Hash) :- weak_server(Pass,Hash).

weak_client(Pass,Hash) :- hash(Pass,Hash), rainbow(Pass,Hash).
weak_server(Pass,Hash) :- rainbow(Pass,Hash), hash(Pass,Hash).
```

#### Example 3

If you're still not sold on the idea, I have one final motivating example. Even
in the purely logical implementations of Datalog, dataflow problems exist.
Stratified negation is indispensible in Datalog programming. When discussing
negation, the emphasis is always on the lack of cyclic dependencies between
predicates used negatively. However, there is another syntactic problem.
Consider the following rule:

```prolog
accessed("Mistral").
accessed("Hattie").
accessed("Rebecca").

password("Hattie" ,"171717").
password("Rebecca","242424").

guest(User) :- not password(User,Pass).

?- accessed(User), guest(User).
```

This program poses the query "out of those who are known to access the
system, which ones are guests?". Being a guest is defined as not having a
password recorded for the given user identifier. This is a stratified program,
so semantically negation should be fine. Yet most implementations would reject
this program because Datalog semantics is also based on [Herbrand
Universes](https://en.wikipedia.org/wiki/Herbrand_structure#Herbrand_universe).
This means we can only conclude facts about constants that are known to the
system. In this example, we can only conclude positive or negative negative
facts about Mistral, Rebecca, and Hattie, but not about Jessica.

In principle, this should be fine because the values `User` variable can take
are already restricted by the `accessed(User)`{.prolog} subgoal in the query.
However, most implementations of Datalog would reject this as this subgoal does
not appear directly within the rule of $guest$ and before the negated subgoal.
This is a conservative approximation. Notice that we have not used any
extralogical predicates, yet negated subgoals automatically require all
variables appearing inside them to be bound by the subgoals preceding them. This
is precisely the problem we have with extralogical predicates.

### Overall sentiment

The chances are if you chose a declarative language such as Datalog over an
imperative alternative, these sort of details are exactly what you are trying to
run away from. It seems here we're forced to choose between useful functionality
and high-level programming. The work that follows allows you to have both and
do so without incurring a runtime performance penalty.

## Understanding invocation safety

Although the examples illustrate the problems with extralogical predicates, they
do not provide us anything concrete to compute with. We need a way of
representing bindings of parameters and dataflow requirements in the program.
As soon as we define these, the precise definition of invocation safety is
simple.

### Adornments: conrete parameter binding

*Adornments* indicate whether a parameter is bound or not. *Adornment
transformation* is the standard analysis that computes it. Let's understand this
using [Example 1](#example-1):

```prolog
auth(User) :- password(User,Pass), hash(Pass,Hash), valid(User,Hash).
```

Is the argument `Pass` in the subgoal `hash(Pass,Hash)`{.prolog} bound? Yes, it
is because the preceding subgoal `password(User,Pass)`{.prolog} has this
variable in it and its evaluation binds `Pass`. How about the `Pass` argument in
`password(User,Pass)`{.prolog}? It is free because we haven't even seen this
variable before[^existential], there is no way something else could have bound
it. How about the `User` argument appearing in the same subgoal? It depends on
the caller of the $auth$ predicate.

Different queries yield different answers:

  1. `?- auth(U)`{.prolog} asks which users can be authenticated. Since we do
  not know which user to authenticate, the `User` in
  `password(User,Pass)`{.prolog} variable is not bound to a value.
  2. `?- auth("Alice")`{.prolog} asks if Jasmine is authenticated. Since we
  know which user to authenticate, `User` in `password(User,Pass)`{.prolog} is
  bound to a value.

What we learn from that example is the following:

  1. Adornment is a top-down procedure starting from the query, the binding
  information flows down.
  2. Constants such as `"Alice"`{.prolog} are ground, hence are bound.
  3. Variables of a subgoal are bound if they appear in subgoals that precede
  them like `password(User,Pass)`{.prolog} preceding `hash(Pass,Hash)`{.prolog}.
  4. Variables of a subgoal are also bound if the variable appears bound in the
  head of the rule. For example, `?- auth("Alice")`{.prolog} makes `User` in
  the head of the $user$ rule bound. Consequently, `User` in
  `password(User,Pass)`{.prolog} is bound.

These four rules define a top-down procedure for binding. Let's invent something
concrete to compute with. Let's call parameters that are bound in an atomic
formula `b` and those that are free `f`. We can then define binding (or
adornment) patterns for atomic formula. From the example above,
`auth("Alice")`{.prolog} would have the pattern `b` due to the constant,
`password(User,Pass)`{.prolog} would have `ff` or `bf` depending on if `User` is
bound in the head of the rule, and `hash(Pass,Hash)`{.prolog} would have `bf`.
As an exercise you can try to figure out the binding pattern for
`valid(User,Hash)`{.prolog} from the previous example (the answer[^exercise]).

#### Example 4

Before moving on from adornments, let's look at an extension of Example 2. There
is something that brings us closer to the solution of the code duplication
problem described above.

```prolog
?- check_client("123456").
?- check_server("deadbeaf").

check_client(Pass) :- weak(Pass,Hash).
check_server(Hash) :- weak(Pass,Hash).

weak(Pass,Hash) :- hash(Pass,Hash), rainbow(Pass,Hash).
```

This is the same program in [Example 2](#example-2) except that we have two
queries one using the $check\_client$ predicate and the other using
$check\_server$. Now let's adorn this program but rather than noting the
adornment patterns separately, let's make them suffixes to the names of the
predicates. This is how this analysis is usually conduct and is the reason why
it is referred as a transformation despite being an analysis in spirit. As it is
a top-down procedure we start from the queries.

```prolog
?- check_client_b("123456").
?- check_server_b("deadbeaf").
```

Both queries receive the pattern `b` because all arguments are constants. Next
we propagate this to the rules defining $check\_client$ and $check\_server$
predicates.

```prolog
check_client_b(Pass) :- weak_bf(Pass,Hash).
check_server_b(Hash) :- weak_fb(Pass,Hash).
```

The heads of each predicate receive their adornments directly from their
callers. Since both callers have the pattern `b`, so do the heads. Now in the
bodies, we have $weak\_bf$ and $weak\_fb$ predicates because
`check_client_bf(User)`{.prolog} binds the first parameter of
`weak(Pass,Hash)`{.prolog} and
`check_client_fb(User)`{.prolog} binds the second parameter of
`weak(Pass,Hash)`{.prolog}. Since
we have two different bindings for $weak$, we need two versions of $weak$ body.

```prolog
weak_bf(Pass,Hash) :- hash_bf(Pass,Hash), rainbow_bb(Pass,Hash).
weak_fb(Pass,Hash) :- hash_fb(Pass,Hash), rainbow_bb(Pass,Hash).
```

The adornment of these rules are done exactly as before, so I won't describe
them again. The important point is the adornment patterns of subgoals are
effected by the adornments patern of the head. The binding patterns of `hash`
above are `bf` and `fb` and this difference stems only from the head of the
tules.

This looks remarkably similar to the code duplication solution we found to the
problem described in [Example 2](#example-2). Once again, we ended up with two
different versions of weak with suffixes are `bf` and `fb` instead of `client`
and `server`. This is a spurfluous difference. The other difference is that the
rule with head $weak\_fb$ is not reordered while the one with $weak\_check$
is. So it can't be a solution to the invocation safety on its own, but it is a
step in the right direction and we develop this furter
[below](#generalised-adornment).

### Modes: concrete dataflow requirements

A *mode* is an indication of input/output behaviour. Each predicate logical or
otherwise have a *mode pattern* associated with it. We only need two modes for
Datalog `+` and `?`. If the invocation a predicate is going to be safe,
parameters with mode `+` must be bound and those with mode `?` are always safe
bound or not.

For example, $hash$ from [Example 1](#example-1) has a `+?` pattern because its
first parameter needs to be bound at the time of invocation and the second
parameter may be bound or not. If we evaluate the subgoal
`hash("Hattie","42")`{.prolog}, `"Hattie"`{.prolog} must be there to safely
execute $hash$, but it doesn't matter `"42"`{.prolog} is there because if the
hash of `"Hattie"`{.prolog} is `"0"`{.prolog}, then we can compare
`"0"`{.prolog} and `"42"`{.prolog} safely.  Let's look at $password$ now. That
predicate is a lot like a database table, there are no restrictions on what you
can use to look up values.  Hence, it has the mode pattern `??`. In standard
Datalog, all predicates have `?` mode associated with all of their
parameters[^not].

Let's adopt a scheme of ammending the predicate name with mode patterns to make
things syntactically obvious just as we did in the [adornments
example](#example-4). [Example 1](#example-1) becomes

```prolog
auth_x(User) :-
  password_??(User,Pass), hash_+?(Pass,Hash), valid_??(User,Hash).
```

You notice there is an `x` in place of `f` or `b` for the $auth$ predicate.
That's because we don't know a way of determining modes of user-defined
predicates. Intuitively, dataflow requirements of a user-defined predicate is
some function of the subgoals that define those predicates. Indeed, finding an
finding an effective procedure to precisely determine mode patterns of
user-defined predicates is the only hard part of our quest to ensure invocation
safety. Something we explore in the [solution](#solution).

### Relating adornments to modes (aka. invocation safety)

Remember `b` means the parameter **is bound** and `+` means the parameter
**needs to be bound**. Modes and adornments are clearly related. Their main
differences are:

 * Adornment transformation needs an entry point (a query) and **dataflow
 infromation flows top-down** from heads to the bodies. We don't have a
 procedure for computing modes (yet), but we mentioned the predicates defined in
 the heads should be a function of those. This suggests **bottom-up information
 flow**.
 * Binding (adornment) patterns **qualify subgoals** (predicates
 applied to tuples of variable and constants). Mode patterns, on the other hand,
 **qualify predicates** and hence don't change from one subgoal to another.
 * Related to the previous point, adornment is entirely dependent on the query,
 whereas modes are not. This suggests we can perhaps compute modes beforehand
 and consult them as queries change.

The agreement between adornments and modes be made precise: in an adorned
program, invocations of extralogical predicates are safe when all subgoals with
extralogical predicates are adorned with `b` for parameters with mode `+`. This
is to say **if it needs to be bound, it is bound.** (Told you it was trivial.)

In the literature, invocation safety is called _well-modedness_. A well-moded
query and program pair doesn't produce invocation errors just like "well-typed
programs don't go wrong" as [Robin
Milner](https://en.wikipedia.org/wiki/Robin_Milner) put it.

## Solution

Now we start with the stupidest possible thing we can do and refine our
approach.

### Naïve solution

The examples so far suggest that it is a simple reordering program of rule
bodies. So why not let's give this a go. Recall the variation of [Example
1](#example-1) with [mode
embellishments](#mode-summarising-dataflow-requirements):

```prolog
auth_x(User) :-
  password_??(User,Pass), hash_+?(Pass,Hash), valid_??(User,Hash).
```

Let's adorn versions of this clause with the subgoals permuted with respect to
the query `?- auth_x(User)`{.prolog}. The heads of the clauses are omitted as
they are always `auth_x_f(User)`{.prolog}.

```prolog
password_??_ff(User,Pass), hash_+?_bf(Pass,Hash), valid_??_bb(User,Hash).
password_??_ff(User,Pass), valid_??_bf(User,Hash), hash_+?_bb(Pass,Hash).
valid_??_ff(User,Hash), password_??_bf(User,Pass), hash_+?_bb(Pass,Hash).
valid_??_ff(User,Hash), hash_+?_fb(Pass,Hash), password_??_bb(User,Pass).
hash_+?_ff(Pass,Hash), valid_??_fb(User,Hash), password_??_bb(User,Pass).
hash_+?_ff(Pass,Hash), password_??_fb(User,Pass), valid_??_bb(User,Hash).
```

The last three are well-moded while the first three are not. Since $hash$ the
only predicate with a binding requirement, namely on its parameters. Orderings
that leads to a bound mode (`b`) at the first parameter are well-moded, while
the others are not.

The obvious problem is if there are $n$ subgoals we may need to adorn $n$
factorial orderings to find a suitable ordering. But perhaps that's not a big
problem in practice if programmers stick to 3 to 5 subgoals per clause. The real
problem is that we cannot isolate clauses.

#### Example 5

Let's say we do some software engineering and factor
`hash_+?(Pass,Hash)`{.prolog} and `valid_??(User,Hash)`{.prolog} into a new
clause with head predicate $check$ as follows:

```prolog
?- auth_x(User)
auth_x(User) :- check_xx(User,Pass), password_??(User,Pass).
check_xx(User,Pass) :- hash_+?(Pass,Hash), valid_??(User,Hash).
```

Now let's try adorning this program while considering different orderings of
$check$ as that is where the extralogical predicate $hash$ occurs.

```prolog
?- auth_x_f(User)
auth_x_f(User) :- check_xx_ff(User,Pass), password_??_bb(User,Pass).

check_xx_ff(User,Pass) :- hash_+?_ff(Pass,Hash), valid_??_fb(User,Hash).
check_xx_ff(User,Pass) :- valid_??_bf(User,Hash), hash_+?_fb(Pass,Hash).
```

This looks like bad news because when we reorder $check$ alone, neither of the
orderings lead to an adornment that makes invocation of $hash$ safe. They both
are make the first parameter free.

At this point we can just say that we have a sound but incomplete analysis,
tough luck. Alternatively, we recognise that the first parameter of the subgoal
with $hash$ is `Pass` which appear in the head of the clause. As we learn in
[adornment transformation rules](#adornments-summarising-binding-of-parameters),
if a parameter is bound in the head then it is also bound in the body. So all we
need is to turn the `ff` binding pattern of the head to `fb` or `bb`. This is
indeed possible if we reorder the use of $check$ within the $auth$ clause as
follows:

```prolog
?- auth_x_f(User)
auth_x_f(User) :- password_??_ff(User,Pass), check_xx_bb(User,Pass).

check_xx_bb(User,Pass) :- hash_+?_bf(Pass,Hash), valid_??_bb(User,Hash).
check_xx_bb(User,Pass) :- valid_??_bf(User,Hash), hash_+?_bb(Pass,Hash).
```

After permuting subgoals with $password$ and $check$, we end up with `bb`
adornment for the head of $check$ and regardless the order of subgoals in the
body $check$. This makes invocations of $hash$ safe in both cases.
Computationally, however, this is problematic. Search space is exponential not
only in the size of individual bodies but it is a multiplication of all possible
orderings of all clauses from query down to the relevant clause. This is
intractable even for small more programs. Now we tackle this problem.

### Greed is good

We can't do better than exponential asymptotically, but we can make it
exponential the way Hindley-Milner type inference is---only in degenerate cases.

**The most important insight** to our solution is the following: although
dataflow requirements are inherent to the predicates, they are conceptual. That
is to say if a predicate parameter has mode `+` (requiring it to be bound) and
the subgoal using that predicate has the variable `V` at that parameter, if a
preceding subgoal already binds `V`, we can safely pretend as if the predicate
has mode `?` in this context. So we can treat

```prolog
... :- password_??(User,Pass), hash_+?(Pass,Hash), ...
```
as
```prolog
... :- password_??(User,Pass), hash_??(Pass,Hash), ...
```

so $hash$ in that context behaves as if it is a logical predicate.

Now we exploit the contextual nature of dataflow. We schedule subgoals with no
dataflow requirements first such as $password$ and $valid$. These subgoals can
be freely placed anywhere in the body as they are always safe to execute. So we
**adopt a greedy approach** and schedule subgoals with such predicates as early
as possible.

The benefits of this approach are two fold:

 1. Combinatorially, there are fewer orderings to consider as placement of
 logical subgoals are restricted.
 2. Variables of scheduled subgoals are propagated to the remaining alternatives
 to relax the dataflow constraints as described above. This would lead to
 further opportunities to apply the greedy schedule.

Scheduling of subgoals fit nicely into a graph where the edges are labelled with
subgoals to schedule and orderings are the paths from the root to vertices with
no successors.

#### Example 6

Let's apply this strategy to [Example 1](#example-1):

```prolog
auth_x(User) :-
  password_??(User,Pass), hash_+?(Pass,Hash), valid_??(User,Hash).
```

The corresponding graph is:
```
     {password, valid}             {hash}
V0 --------------------> V1 -------------------> V2
```

This graph stores orderings where subgoals with predicates $password$ and
$valid$ are scheduled first and it doesn't matter in which order, only then the
subgoal with predicate $hash$ is scheduled.

The subgoals with predicates $password$ and $valid$ could be scheduled first
because they have no dataflow requirements (indicated by `??` mode pattern).
The subgoal with $hash$ could not be scheduled at that point due to `+?` mode
pattern. However, as we established earlier in this section, mode
patterns can be relaxed at a given context. So if we treat the vertex `V1` in
the graph as a context, `hash_+?(Pass,Hash)` behaves as `hash_??(Pass,Hash)`
because on this path the subgoal `password(User,Pass)` precedes it and binds
`Pass`, thus we can schedule it at that point using the greedy principle.

More concretely, this leads to the following orderings:

```prolog
password_??(User,Pass), valid_??(User,Hash), hash_+?(Pass,Hash).
valid_??(User,Hash), password_??(User,Pass), hash_+?(Pass,Hash).
```

These are the two of three well-moded orderings found through brute-force search
in [naïve solution](#naïve-solution) described above. Compared to that solution,
we are missing one valid ordering. The ordering we miss have
`valid_??(User,Hash)` at the end of the body. Greedy scheduling prevents us to
discover this ordering.

This raises the question **"are there cases in which we discard the only safe
ordering?"** The answer is no. If there is at least one safe ordering that can
be found by reordering, greedy scheduling will also find at least one valid
ordering. Surprisingly, _greed is good_[^greed] and it doesn't compromise
completeness.

Before we move on to other examples of scheduling graphs, we can finally answer
the pending question of mode patterns for user-defined predicates posed [where
modes are introduced](#modes-summarising-dataflow-requirements).

### Modes of user-defined predicates

Let's continue with [Example 6](#example-6) and deduce what `x` in
`auth_x(User)` should be.

Since a mode marks a requirement of boundness, `x` should be `+` if `User` needs
to be bound for the invocation to be safe and it should be `?` if invocation of
all predicates in the body are safe regardless binding status of `User`.
Technically, if it is safe with a `?` mode, then it is also safe with a `+`
modes, so we are looking for the most relaxed mode[^principal-moding]. The
orderings from the graph above didn't make any conditional reasoning about
boundedness of `User`, hence `?` is suitable for $auth$. We can revise the two
versions of the cluase as follows:

```prolog
auth_?(User) :-
  password_??(User,Pass), valid_??(User,Hash), hash_+?(Pass,Hash).
auth_?(User) :-
  valid_??(User,Hash), password_??(User,Pass), hash_+?(Pass,Hash).
```

#### Example 7

Let's now look at [Example 5](#example-5) again:

```prolog
?- auth_x(User)

auth_x(User) :- check_xx(User,Pass), password_??(User,Pass).
check_xx(User,Pass) :- hash_+?(Pass,Hash), valid_??(User,Hash).
```

Let's look at the interesting scheduling graph first that is the one for for
`check` at the head.

```
     {valid}        {hash}
V1 ----------> V2 ---------> V3
```

This graph looks similar to the previous one. We apply the greedy principle and
schedule `valid_??(User,Hash)`{.prolog} first. The difference is the variable
bound by this subgoal (`User` and `Hash`) don't include `Pass` which is the
variable at the dataflow restricted parameter of `hash_+?(Pass,Hash)`{.prolog}.
So the only way we can schedule $hash$ is that we require `Pass` to be bound
from the moment we start evaluating the rule. This is same as saying the second
parameter of $check$ (which is `Pass`) has to be bound. For the first parameter,
there are no restrictions posed. Then the overall mode pattern for check is
`?+`.

In the description above, we kept track of which variables on the path has to be
resolved by the invoker of the predicate being defined. This information can
naturally be stored in the vertices as an accumulator. This is indeed how it is
done in the paper but we elide the details here to simplify the presentation.

Now that we know the mode pattern for $check$, we can draw a scheduling graph
for the rule that defines $auth$ and deduce its predicate (again). This time we
do not give a detailed explanation. It'd be a good exercise to see why we
scheduled which predicate and why and what the mode pattern of $auth$ is.

```
     {password}        {check}
V1 -------------> V2 ----------> V3
```

We cheat here a bit and impose an order on building the graphs. In general, we
can't find such an order because rules can refer to themselves recursively or be
mutually recursive with other clauses. Proper way of handling that situation is
to assume `?` in place of `x` for modes of user-define predicates initially, and
repeatedly apply this graph-based analysis to update the patterns until we reach
stable mode patterns (fixpoint) for all user-define predicates. You can refer to
the paper on why this works and why it terminates at all.

#### Example 8

So far it looks like all the scheduling graphs are just single paths. This is
not the case in general and we can use [Example 2](#example-2) to demonstrate
it:

```prolog
weak_xx(Pass,Hash) :- hash_+?(Pass,Hash), rainbow_?+(Pass,Hash).
```

We don't have any logical predicates in this body. This can't be a good start.
There is only one thing we do, that is to default to brute-force search for a
moment and try scheduling both subgoals.

```
      {hash}          {rainbow}
  -------------> V2 -------------> V3
 /
V1
 \
  -------------> V5 -------------> V6
    {rainbow}           {hash}
```

Finally, some more interesting `ASCII` art.

Let's inspect the branch we try scheduling `hash_+?(Pass,Hash)`{.prolog} first.
In this path, scheduling the subgoal with $hash$ predicate binds `Pass` and
`Hash`, as a result at the context of $V2$, rainbow behaves like a logical
predicate (the dataflow constrained second parameter has `Pass` which is already
bound). Since we couldn't schedule hash the subgoal with $hash$ for free, it
seems we need to constraint the first parameter (`Pass`) of $weak$ leading `+?`
mode pattern.

But wait a second! if we inspect the other branch instead, we commit to
requiring `Hash` to be bound in the head of the rule (and consequently dealt
with by the caller) instead. This suggests a mode pattern `?+`.

So which is it? In a way, it is both. Depending on the ordering of the clauses
we have different dataflow requirements. This is good! Now we can just select a
representitive ordering for each mode pattern. When the clause is used
differently, we use the appropriate ordering. So the overall mode pattern of
$weak$ is `+?/?+` to signify either of them can be used.

One reason we ended with two alternatives is that the mode patterns we obtained
are incomparable. If we had options `+?` and `++`, instead we could have
discarded `++` because `+?` is a more favourable alternative. This allows us to
store fewer orderings. We say more about that in the paper.

### Multiple rules

So far we have been assuming that a predicate is defined by a single rule. Now
we look at those defined by multiple rules. Let's extend [Example 8](#example-8)
to have a custom extralogical predicate that checks weakness of a password hash
pair and requires both of them to execute safely.

```prolog
weak_xx(Pass,Hash) :- hash_+?(Pass,Hash), rainbow_?+(Pass,Hash).
weak_xx(Pass,Hash) :- custom_weak_++(Pass,Hash).
```

We already know the first rule leads to the mode pattern `+?/?+`. The second
rule is so simple that we can tell the mode pattern it leads without drawing the
relevant scheduling graph, namely `++` inherited from its single defining
subgoal.

Now what does it mean to invoke a predicate in Datalog? It means we are going to
try each of its defining rules to collect all possible conclusions. This implies
any invocation of $weak$ is going to evaluate both rules. Therefore, the only
thing we can do to ensure safety is to satisfy the dataflow requirements of each
clause simultaneously. What this means for our example is that we generate all
possible combinations that is `++` & `+?` and `++` & `?+`. In each case, `++` is
stricter for every parameter, so it shadows the other. Hence, we end up with
`++/++`, but since both alternatives are identical, the overall mode pattern for
$weak$ is `++`.

This is the second time we are combining mode patterns and there is a form of
subsumption going on. When we consider two alternative dataflow requirements and
their combination leads to a more relaxed mode pattern. When we combine two mode
patterns that need to be satisfied simultaneously, the combination is more
strict. You must have noticed that these two operations sound very algebraic.
Indeed, to our surprise, they form [Martelli's
semiring](https://www.cl.cam.ac.uk/teaching/0910/L11/L11_04_08.pdf) (sorry,
there aren't any non-academic resources I could find) originally used to compute
cutsets of a graph. To the best of my knowledge this hasn't been used in
dataflow context before and seems general enough to be used beyond Datalog and
extralogical predicates.

### Generalised adornment

Now we know how to determine dataflow requirements of user-defined predicates as
well as orderings of subgoals that lead to these requirements. However, this
does not help very much with our definition of [invocation
safety](#relating-adornments-to-modes-aka.-invocation-safety). The reason is
that definition rely on adorning a program in the given order of subgoals. This
is already in the result of [Example 4](#example-4) with two different versions
of the $weak$ clause with different adornments but static ordering of subgoals.

So the final step in our quest to invocation safety is to generalise adornment
procedure such that it can take reorderings into the account.

We modify the adornment procedure in a single way. We let the procedure take a
reordering function that given a clause and a binding pattern produces an
ordering. Of course, we compute these orderings through scheduling graphs as
above. Then, right before we start adorning the body of a clause, we apply the
reordering first, then adorn from left to right as usual.

#### Example 9

Consider the following example adapted from [Example 4](#example-4).

```prolog
?- weak_+?/?+(Pass,"deadbeaf").

weak_+?/?+(Pass,Hash) :- hash_+?(Pass,Hash), rainbow_?+(Pass,Hash).
```

So the head of $weak$ clause will have the adornment `fb` due to the query. We
almost computed the ordering function for $weak$ in [Example 8](#example-8). For
`?+` mode pattern alternative which is the only alternative compatible with `fb`
binding pattern, we have an ordering in which the subgoal with $rainbow$ comes
first and the subgoal with $hash$ come second. So we reorder the body first and
then perform the adornment and that leads to the following adorned program:

```prolog
?- weak_+?/?+_fb(Pass,"deadbeaf")

weak_+?/?+_fb(Pass,Hash) :- rainbow_?+_fb(Pass,Hash), hash_+?_bb(Pass,Hash).
```

And voilà, we have a $rainbow$ subgoal with an adornment for its second
parameter `b` and $hash$ subgoal with an adornment for its first parameter `b`
as required. As all extralogical predicates are used in subgoals with adornments
that match their modes, the program is safe to invoke.

### Checking invocation safety

Once we compute modes for all-user defined predicates including the query, we
don't have to adorn the program to see if the program is well-moded. We only
need to look at the query.

#### Example 10

In [Example 9](#example-9) the query was `?-
weak_+?/?+_fb(Pass,"deadbeaf")`{.prolog}, here the fact that `fb` is consistent
with one of the mode pattern alternatives, namely `?+` immediately indicates
that we have a ordering function that satisfy all dataflow requirements.

If, on the other, hand we pose the same query to the version of weak used in
explaining [modes of predicates with multiple rules](#multiple-rules):

```prolog
?- weak_++(Pass,"deadbeaf")

weak_++(Pass,Hash) :- hash_+?(Pass,Hash), rainbow_?+(Pass,Hash).
weak_++(Pass,Hash) :- custom_weak_++(Pass,Hash).
```

Just by looking at the query, we know the program is not well-moded with respect
to this query because the predicate $weak$ in this case requires both of its
parameters to be bound but the first argument to the query is the free variable
`Pass`.

### Some properties

This algorithm enjoys a number of properties. I am neither going to get into
their proofs nor the mathematical details, but it would be amiss to omit them
entirely:

 1. Soundness: if the algorithm finds a reordering function for a program, the
 the reordered rules won't have invocation safety.
 2. Completeness: if there are any orderings of clauses that ensure invocation
 safety, then the algorithm will find a (possible different) set of orderings
 that ensure invocation safety.
 3. Incremental computation: addition of new rules don't invalidate the old
 results, hence the mode patterns of existing user-defined predicates can be
 used to seed the analysis leading to faster execution.
 4. Termination: the analysis terminates on all inputs.

In particular, incremental computation is useful for making this analysis
scalable. In the specical case that the added rule does not extend an existing
predicate, _i.e._, have a freash head, we don't have to reanalyse old rules.
This means we can analyse libraries and ship the mode patterns of predicates
defined in the library with them. The users of the library won't have to
reanalyse the code in the library.

## Summary & concluding thoughts

The main take away is declarative programming is awesome! In the case of
Datalog, we can supplement expressivity by allowing extralogical predicates.
This brings the syntactic order of execution problem with it, but our analysis
completely eliminates this and restores the promise of declarative programming!

The analysis relies on computing dataflow requirements (modes) of user-defined
predicates and verifying their consistency with respect to the actual bindings
(adornments) of the program and query pairs.

We avoid inefficiency through a greedy scheduling algorithm, but we don't
sacrifice completeness. Additionally, our analysis is incremental and thus
scalable to multi module programs with relative ease.

Here are few reasons why you might like to read the paper:

 * understanding the mathematical foundation for modes & bindings,
 * gaining insights into about an implementation (paper is effectively
 executable maths),
 * need more advanced examples (illustrating omitted aspects of the algorithm),
 * and looking for generalisation from Datalog to other contexts.

There are number of directions this work may go. I believe the constraint-based
approach of the paper can be generalised to other declarative languages which
need more sophisticated modes. I firmly believe there is a fundamental link
between Martelli's semiring and dataflow in general. We didn't discuss
user-level annotations as you noticed. There are interesting design questions
about an annotation language for modes that might work exploring. Finally (and a
bit more abstractly), extralogical predicates are inevitable in logic
programming but they are afterthoughts to clear declarative semantics. I'd like
them to be first-class citizens so we can reason about them and analyse them
better.

[^existential]: `Pass` in this rule is an existentially quantified variable, so
there is indeed nothing that could have bound it out of the rule context.

[^not]: This seems to contradict what I said in [Example 3](#example-3), so let
me clarify. In a subgoal like `not r(X,Y,Z)`{.prolog}, the predicate $r$ still
has `???` mode pattern. It is the negation that imposes makes `r` behave as if
it has `+++` pattern.

[^exercise]: It is `bb` because both `User` and `Pass` appear in preceding
subgoals.

[^greed]: This is a quote from a famous movie speech by the character [Gordon
Gekko](https://en.wikipedia.org/wiki/Gordon_Gekko) in [Wall
Street](https://www.rottentomatoes.com/m/wall_street). Highly
recommended.

[^principal-moding]: In the paper, we show and heavily use the fact that
constraints (which are derived from modes) form a bounded partial order.  We can
talk about _principal moding_ or _sub moding_, but they are only relevant if we
have explicit annotations for modes which are not strictly necessary for safety
checking and automated reordering. Perhaps another paper? Feel free to contact
me if you want to discuss this more.
