---
title: Compiler Construction Example Sheet I
date: 2018-01-06
lastUpdated: 2021-02-07
---

1. Build and play with the SLANG compiler. Experiment with the front end
(syntax/type checker) and be prepared to discuss what you have done in the
supervision. It is OK if the changes you make do not work.

2. Write down a _pipeline_ of steps involved in compilation paying special
attention to what goes into each step and what goes out. You can be as vague or
specific as you want, but be prepared to discuss compiler related concepts and
how it fits to your pipeline.

3. How is LLVM approach to compiler construction is different than that is
presented in this course?

4. Why are functional languages are commonly used to prototype compilers?

5. Why does `past.ml` in first Slang compiler have `loc` parameter for every
constructor, while the corresponding constructors in `ast.ml` don't have them?

6. According to lexical analysis algorithm described in slide 31, what are the
two rules that disambiguate multiple possible matches out of the same character
stream?

7. Starting with regular expressions that match individual tokens, how do we
generate a single lexing program?

8. What is the difference between concrete and abstract syntax trees (CST vs
AST)? What stages of compilation involve these?

9. What does it mean for a grammar to be ambiguous? How can this ambiguity be
resolved?

10. How does a recursive descent parser work? What class of languages can it be
used to describe? What are the problems with it?

11. How does a shift-reduce parser work? What class of languages can it be used
to describe? What problems of recursive descent parser does it address?

12. [2012/3/4](http://www.cl.cam.ac.uk/teaching/exams/pastpapers/y2012p3q4.pdf) (a) (b)

13. [2015/3/3](http://www.cl.cam.ac.uk/teaching/exams/pastpapers/y2015p3q3.pdf)

14. Consider a language of arithmetic expressions using `*`, `/`, `+`, `-`
operators, operating on integers, and allowing paranthesised expressions.

    a. Design a grammar for this language taking operator precedence into
    account.

    b. Write a hand-coded lexer and a recursive descent parser for this grammar
    in OCaml. Clearly explain any transformations you made to your original
    grammar to accomplish this.

    c. Write a computer generated lexer and parser using `ocamllex` and `menhir`
    OCaml packages. You might like to consult [this
    tutorial](https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html)
    to learn more about the tools.

Thanks to Zébulon Goriely for catching a typo.
