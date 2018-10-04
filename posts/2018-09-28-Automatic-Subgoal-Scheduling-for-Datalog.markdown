---
title: Automatic Subgoal Scheduling for Datalog
postType: Technical
inWhich: we talk about how to make Datalog safer by reordering subgoals
  statically when predicates with dataflow constraints are involved.
---

I recently presented "Automatic Reordering for Dataflow Safety of Datalog" (can
be accessed freely if you follow the link from [my
homepage](https://dodisturb.me)) in the 20th Symposium on Principles and
Practice of Declarative Languages. A few commented that the paper is technically
dense and consequently hard going. I don't want this work to be ignored because
I suck at writing. So in an attempt to make things right and also to do some PR,
I will explain the major ideas of the paper without the formalism and with
examples.

I start by describing what extralogical predicates are, why one might want them
in Datalog, and what problems they bring with them. Then I get to the
bottom of what it means to safely evaluate subgoals using such predicates. This
will lead us to the naïve, incomplete, and inefficient solution and that will
lead us to our solution. I'll conclude by giving some pointers where this work
might go and why you might like to look at the paper.

## Motivation

#### Example 1

Here's a hypothethical Datalog _rule_ that authenticates a user.

```prolog
auth(User) :- password(User,Pass), hash(Pass,Hash), valid(User,Hash).
```

The reading of any rule in Datalog is "if everything (_subgoals_) to the right
of `:-`{.prolog} holds, then we can conclude the thing (atomic formula) on the
left." In this specific case, we can authenticate a user if we have a password
for a given user and the hash of that user is known to be valid. One of the
nicest parts of this reading is that it doesn't matter which order the
subgoals are presented, we still reach the same conclusion. For example,
```prolog
auth(User) :- hash(Pass,Hash), password(User,Pass), valid(User,Hash).
```
would authenticate exactly the same users as the previous example.

Each atomic formula (more specifically each subgoal) contains a predicate for
example $password$ is the predicate of the subgoal `password(User,
Hash)`{.prolog}. When the predicates in a program are _logical_, there are no
dataflow restrictions for evaluation of a subgoal with that predicate. For
example, `password("Milner",Pass)`{.prolog} would bind the password of Milner to
`Pass` while `password(User,Pass)`{.prolog} would generate all known user and
password pairs. There are no inherent input and output parameters to a logical
predicate.

However, the $hash$ predicate stands out in the previous example because hash
functions (if they are any good) work only in one direction. It is unreasonable
to expect $hash$ to bind a value for the password given an hash. Let's refer to
predicates like $hash$ (those with dataflow requirements) as _extralogical_
predicates.

In light of this knowledge, the two versions of the rule defining the
predicate $user$ above are not equivalent. Evaluation of the subgoal
`hash(Pass,Hash)`{.prolog} produces a runtime error if the value of `Pass` is
unknown.  Suddenly, we have to be careful about the way you order your subgoals
and not only those that are obviously extralogical like $hash$ but also any
user-defined logical predicate that uses an extralogical one. To make the
matters worse, although semantically arithmetic relations such as $>$ are
logical, they are usually implemented as extralogical predicates.

#### Example 2

Just when you think things are looking bleak, it gets worse. Extralogical
predicates may also cause code duplication. Let me demonstrate this with another
example.

```prolog
check_client(Pass) :- weak(Pass,Hash).
check_server(Hash) :- weak(Pass,Hash).

weak(Pass,Hash) :- hash(Pass,Hash), rainbow(Hash,Pass).
```

In this example, we define a relation $weak$ that checks if a password or a hash
is weak that is to say the hash of the password can be found by a rainbow
function (a function that can reverse some hashes). Like $hash$, $rainbow$ is
also extralogical. Now it is beneficial for both the client and the server to
check if a hash is weak, but the the client shouldn't know the hash of a given
password (otherwise it can construct a rainbow table of its own!) and the server
shouldn't know the password (in case it gets stolen). Hence, there are two
predicates `check_server` that takes a password and `check_server` that takes a
hash that can be used by the client and server respectively.

This example is worse than the previous one because regardless how carefuly the
programmer is with the dataflow requirements of its predicates, it wouldn't be
able to rewrite the definition of `weak` in a single rule such that all
binding requirements are satisfied. Now when `check_client` is used, `weak`
should have the subgoal `hash(Pass,Hash)`{.prolog} first as the password is
known (satisfying `hash`'s binding requirement) and evalauting this subgoal
produces a hash, hence satisfying the binding requirement of `rainbow`. If
`check_server` is used the situation is the exact opposite because this time the
hash value is known. So neither of the orderings can be used to satisfy the
requirements of the whole program. The only solution is a code duplicating
rewrite as follows:
```prolog
check_client(Pass) :- weak_client(Pass,Hash).
check_server(Hash) :- weak_server(Pass,Hash).

weak_client(Pass,Hash) :- hash(Pass,Hash), rainbow(Hash,Pass).
weak_client(Pass,Hash) :- rainbow(Hash,Pass), hash(Pass,Hash).
```

#### Example 3

If you're still not sold on the idea, I have one final example. Even in the
purely logical implementations of Datalog, this problem already hides in plain
sight. Stratified negation is an indispensible tool in Datalog logic
programming. When discussing negation, the emphasis is always on the lack of
cyclic dependencies between predicates used negatively. However, there is
another often ignored syntactic problem. Consider the following rule.

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
This means we can only conclude facts about terms that are known to the system.
In this case we can only conclude something positive or negative about Mistral,
Rebecca, and Hattie, but not about Jessica.

In principle, this should be fine because the values `User` variable can take
are already restricted by the `accessed(User)`{.prolog} subgoal in the query.
However, most implementations of Datalog would reject this as this subgoal does
not appear directly within the rule of $guest$ and before the negated subgoal.
This is a conservative approximation. Notice that we have not used any
extralogical predicates, yet negated subgoals automatically require all
variables appearing inside them to be bound by things that precede them. This is
precisely the problem we have with extralogical predicates.

The chances are if you chose a declarative language such as Datalog over an
imperative alternative, these sort of details are exactly what you are trying to
run away from. It seems here we're forced to choose between useful functionality
and high-level programming. The work described here allows you to have both and
without incurring a runtime performance penalty.

## Understanding invocation safety

Although the examples illustrate the problems with extralogical predicates, they
do not provide us anything concrete to compute with. We need a way of
representing dataflow requirements and binding of parameters in the program.
As soon as we define these, the precise of invocation safety (or well-modedness
as it is referred in the literature) is simple (I'd say trivial, but that puts
people off. You'll definitely agree with me once we get there).

### Adornments: summarising binding of parameters

*Adornments* indicate the binding status of an argument. *Adornment
transformation* is the standard analysis that computes it (I am well aware that
calling an analysis a transformation is silly). Let's understand using [Example
1](#example-1):

```prolog
auth(User) :- password(User,Pass), hash(Pass,Hash), valid(User,Hash).
```

Is the argument `Pass` in the subgoal `hash(Pass,Hash)`{.prolog} bound? Yes, it
is because the preceding subgoal `password(User,Pass)`{.prolog} has this
variable in it and its evaluation binds `Pass`. How about the `Pass` argument in
`password(User,Pass)`{.prolog}? It is free because we haven't even seen this
variable before[^1], there is no way something else could have bound it. How
about the `User` argument appearing in the same subgoal? It depends on the
caller of the $auth$ predicate.

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
`valid(User,Hash)`{.prolog} from the previous example (the answer[^3]).

#### Example 4

Before moving on from adornments, let's look at an extension of Example 2. There
is something that brings us closer to the solution of the code duplication
problem described above.

```prolog
?- check_client("123456").
?- check_server("deadbeaf").

check_client(Pass) :- weak(Pass,Hash).
check_server(Hash) :- weak(Pass,Hash).

weak(Pass,Hash) :- hash(Pass,Hash), rainbow(Hash,Pass).
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
`check_client_bf(User)` binds the first parameter of `weak(Pass,Hash)` and
`check_client_fb(User)` binds the second parameter of `weak(Pass,Hash)`. Since
we have two different bindings for $weak$, we need two versions of $weak$ body.

```prolog
weak_bf(Pass,Hash) :- hash_bf(Pass,Hash), rainbow_bb(Hash,Pass).
weak_fb(Pass,Hash) :- hash_fb(Pass,Hash), rainbow_bb(Hash,Pass).
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

### Modes: summarising dataflow requirements

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
parameters[^2].

Let's adopt a scheme of ammending the predicate name with mode patterns to make
things syntactically obvious just as we did in the [adornments
example](#example-4). [Example 1](#example-1) becomes

```prolog
auth_x(User) :- password_??(User,Pass), hash_+?(Pass,Hash), valid_??(User,Hash).
```

You notice there is an `x` in place of `f` or `b` for the $auth$ predicate.
That's because we don't know a way of determining modes of user-defined
predicates. Intuitively, dataflow requirements of a user-defined predicate is
some function of the subgoals that define those predicates. Indeed, finding an
finding an effective procedure to precisely determine mode patterns of
user-defined predicates is the only hard part of our quest to ensure invocation
safety. Something we explore in the [solution](#solution).

### Relating adornments to modes (aka. invocation safety)

Remember `b` means the parameter **is** bound and `+` means the parameter
**needs** to be bound. Modes and adornments are clearly related. Their main
differences are:

 * Adornment transformation needs an entry point (a query) and flows top-down
 from heads to the bodies. We don't have a procedure for computing modes (yet),
 but we mentioned the predicates defined in the heads should be a function of
 those. This suggests bottom-up information flow.
 * A binding (adornment) pattern qualifies or embellishes a subgoal (a predicate
 applied to tuples), hence varies depending on the context. A mode pattern, on
 the other hand, qualifies the predicate and hence does not change from one
 subgoal to another.
 * Related to the previous point, adornment is entirely dependent on the query,
 whereas modes are not. This suggests we can perhaps compute modes beforehand and
 consult them as queries change.

The agreement between adornments and modes be made precise: in an adorned
program, invocations of extralogical predicates are safe when all subgoals with
extralogical predicates are adorned with `b` for parameters with mode `+`. (I
told you it was trivial.)

In the literature, invocation safety is called _well-modedness_. A well-moded
query and program pair does not produce invocation errors just like "well-typed
programs don't go wrong" as [Robin
Milner](https://en.wikipedia.org/wiki/Robin_Milner) put it.

## Solution

Now we start with the stupidest possible thing we can do and refine our
approach.

### Naïve solution

The examples so far suggest that it is a simple reordering program of rule
bodies. So why not let's give this a go. Recall [Example 1](#example-1):

```prolog
auth(User) :- password(User,Pass), hash(Pass,Hash), valid(User,Hash).
```

### Brute-forcing our way through the problem

### Greed is good

### Multiple rules

### Generalised adornment

## Conclusion

[^1]: `Pass` in this rule is an existentially quantified variable, so there is
indeed nothing that could have bound it out of the rule context.

[^2]: This seems to contradict what I said in [Example 3](#example-3), so let me
clarify. In a subgoal like `not r(X,Y,Z)`{.prolog}, the predicate $r$ still has
`???` mode pattern. It is the negation that imposes makes `r` behave as if it
has `+++` pattern.

[^3]: It is `bb` because both `User` and `Pass` appear in preceding subgoals.
