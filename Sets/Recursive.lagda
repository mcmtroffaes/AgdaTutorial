% Recursive Sets

Import List
===========

\begin{code}
module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)
\end{code}

The effect of this `open import` declaration is the same as if we copied the
definition of `Bool` type here. Note that we enumerated the constructors of `Bool` too.

More about import declarations come later.


Peano representation
============================

We are looking for a representation natural numbers.
The simplest choice is the *Peano representation* which corresponds to the unary numeral system:

term                    interpretation in decimal form
----------------------- --------------------------
`zero`                  0
`suc zero`              1
`suc (suc zero)`        2
`suc (suc (suc zero))`  3
...                     ...


Definition of `ℕ`
==============

In Agda the definition

\begin{code}
data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ
\end{code}

yields the infinite set of judgements

~~~~~~~~~~~~~~~~~ 
ℕ : Set
zero : ℕ
suc zero : ℕ
suc (suc zero) : ℕ
suc (suc (suc zero)) : ℕ
...
~~~~~~~~~~~~~~~~~

<!--
| *Interpretation:* `ℕ` ∈ `Set`, `ℕ` = { `zero` ~ 0, `suc zero` ~ 1, `suc (suc zero)` ~ 2, ... }
-->

We may use `0`, `1`, `2`, ... instead of `zero`, `suc zero`, `suc (suc zero)`, ...*

************************

*\ Decimal natural number literals can be used if we bind our `ℕ` set to the Agda internals with the following three declarations:

~~~~~~~~
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
~~~~~~~~


Type checking of expressions
=======================

With the Emacs command C-`c` C-`d` one can get Agda to type check
a given expression (`d` stands for 'deduce').

Example: Hit C-`c` C-`d` and enter `suc (suc zero)`. 

Exercise: Try to type-check the following expressions:

-   `suc zero`
-   `suc (zero)`
-   `(suc) zero`
-   `zero suc`
-   `(suc suc) zero`
-   `suc`


Binary representation of `ℕ`
==============

\begin{code}
data ℕ⁺ : Set where
  one      :      ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺
\end{code}

yields (without ordering)

~~~~~~~~~~~~~~~~~ 
ℕ⁺ : Set
one : ℕ⁺
double one : ℕ⁺
double+1 one : ℕ⁺
double (double one) : ℕ⁺
double+1 (double one) : ℕ⁺
double (double+1 one) : ℕ⁺
double+1 (double+1 one) : ℕ⁺
double (double (double one)) : ℕ⁺
...
~~~~~~~~~~~~~~~~~

And

\begin{code}
data ℕ₂ : Set where
  zero :      ℕ₂
  id   : ℕ⁺ → ℕ₂
\end{code}

yields

~~~~~~~~~~~~~~~~~ 
ℕ₂ : Set
zero : ℕ₂
id one : ℕ₂
id (double one) : ℕ₂
id (double+1 one) : ℕ₂
id (double (double one)) : ℕ₂
id (double+1 (double one)) : ℕ₂
...
~~~~~~~~~~~~~~~~~

<!--
| *Interpretation:*
| 
|  - `ℕ⁺` ∈ `Set`, `ℕ⁺` = { `one` ~ 1, `double one` ~ 2, `double+1 one` ~ 3, `double (double one)` ~ 4, `double (double+1 one)` ~ 5, ...}
|  - `ℕ₂` ∈ `Set`, `ℕ₂` = { `zero` ~ 0, `id one` ~ 1, `id (double one)` ~ 2, ...}
-->


Soon we will prove in Agda that `ℕ` and `ℕ₂` are isomorphic with the following relation:

**ℕ**                   **ℕ₂**
----------------------- --------------------------
`zero`                  `zero`
`suc zero`              `id one`
`suc (suc zero)`        `id (double one)`
`suc (suc (suc zero))`  `id (double+1 one)`
...                     ...

*Exercise:* How 9 is represented in `ℕ₂`? Type check the expression!

*Question*: why didn't we use one `data` definition with 4 constructors `zero`, `one`, `double`, `double+1`?



Rationale behind different representations
==========================================

Each representation has its merit.

*Exercise:* Guess which representation (`ℕ` or `ℕ₂`) is better for the following tasks!

 * Computing `n * 2`.
 * Computing `⌊n / 2⌋`.
 * Deciding whether the number is odd.
 * Computing `n + m`.
 * Computing `n * m`.
 * Proving that `n + m` = `m + n` for all `m` and `n`.
 * Storing the number.

*****************

A good strategy is choose the right representation for each task
and convert values between different representations.


Exercise
=========

 * Define `ℤ`!

(Several solutions are possible.)


Binary trees
=========

\begin{code}
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
\end{code}

yields

~~~~~~~~~~~~~~~~~ 
BinTree : Set
leaf : BinTree
node leaf leaf : BinTree
node (node leaf leaf) leaf : BinTree
node leaf (node leaf leaf) : BinTree
node (node leaf leaf) (node leaf leaf) : BinTree
...
~~~~~~~~~~~~~~~~~

`BinTree` elements are good for representing binary trees (just the shapes without data).


*Exercise:* define binary trees according to the following shapes!

~~~~~~~~ {.dot}
Node [shape = point]
Edge [dir = none]
z
o -> z1
o -> z2
x -> a
x -> b
a -> a1
a -> a2
b -> b1
b -> b2
x1 -> x2 -> x3 -> x4
x1 -> x1v
x2 -> x2v
x3 -> x3v
~~~~~~~~



Exercises
=========

*   Define binary trees
    -   with natural number data attached to the leafs
    -   with natural number data attached to the nodes
    -   with Booleans in the nodes and natural numbers in the leafs
*   Define the lists (finite sequences) of natural numbers.
*   Define the non-empty lists of natural numbers.



