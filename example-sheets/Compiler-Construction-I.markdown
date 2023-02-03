---
title: Compiler Construction Example Sheet I
date: 2018-01-06
lastUpdated: 2023-02-03
---

1. Build and play with the SLANG compiler. Experiment with the frontend
(syntax/type checker) and be prepared to discuss what you have done in the
supervision. It is OK if the changes you make do not work.

2. Write down a _pipeline_ of steps involved in compilation paying special
attention to what goes into each step and what goes out. You can be as vague or
specific as you want, but be prepared to discuss compiler related concepts and
how it fits to your pipeline.

3. How is LLVM approach to compiler construction is different than that is
presented in this course?

4. Why does `past.ml` in first Slang compiler have `loc` parameter for every
constructor, while the corresponding constructors in `ast.ml` don't have them?

5. According to lexical analysis algorithm described in the slides, what are the
two rules that disambiguate multiple possible matches out of the same character
stream?

6. Starting with regular expressions that match individual tokens, how do we
generate a single lexing program?

7. What does it mean for a grammar to be ambiguous? How can this ambiguity be
resolved?

8. How does a recursive descent parser work? What class of languages can it be
used to describe? What are the problems with it?

9. [2012/3/4](http://www.cl.cam.ac.uk/teaching/exams/pastpapers/y2012p3q4.pdf) (a) (b)

10. [2022/4/1](https://www.cl.cam.ac.uk/teaching/exams/pastpapers/y2022p4q1.pdf)

11. Consider a language of regular expressions consisting of
    - characters (e.g., `a` matching the string `a`),
    - concatenation operation (e.g., `ab` matching `a` then `b`),
    - alternative operator (e.g., `a|b` matching `a` or `b`),
    - the Kleene star (e.g., `a*` matching zero or more `a`s),
    - a restricted form of character classes with ranges (e.g., `[a-c]` to mean
      matching `a` or `b` or `c`) as well as lists (e.g., `[abc]` to mean matching
      `a` or `b` or `c`),
    - and parantheses (e.g., `a(b|c)` meaning matching `a` followed by matching
      `b` or `c`).

    For this language,
    a. Design a grammar for this language taking operator precedence into
    account (concatenation binds tighter than alternative). Write it down using
    the EBNF notation;

    b. Write a hand-coded lexer and a recursive descent parser for this grammar
    in OCaml. Clearly explain any transformations you made to your original
    grammar to accomplish this;

    c. Write a computer generated lexer and parser using `ocamllex` and `menhir`
    OCaml packages. You might like to consult [this
    tutorial](https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html)
    to learn more about the tools.

Thanks to Zébulon Goriely for catching a typo.
