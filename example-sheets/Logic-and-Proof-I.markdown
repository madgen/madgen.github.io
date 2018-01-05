---
title: Logic and Proof Example Sheet I
date: January 6th, 2018
---

## From the lecture notes

  - Section 2 Exercises: 1, 2, 4
  - Section 3 Exercises: 6, 7
  - Section 4 Exercises: 8, 10, 11

## Exam questions

  - [2010/6/6](http://www.cl.cam.ac.uk/teaching/exams/pastpapers/y2010p6q6.pdf) (b)

## Implementation

Write a program to convert an arbitrary propositional logic formula to CNF.
Formulae involve single capital letter variables and the following operators:

- implies
- and
- or
- not

To prevent you from losing time on parsing you can use prefix notation.

Example input from shell: or (and P Q) R
Example output to shell: and (or P R) (or Q R)

Bonus points if you implement a theorem prover on top of it. (It is not as
difficult as it sounds.)

Please write it in one of the following languages: Haskell, SML, OCaml, Prolog,
Elixir, Ruby, Python, Fortran, C, C++, Java, Scheme, Common Lisp.

You will realise it is much easier to do it in functional languages compared to
procedural ones.
