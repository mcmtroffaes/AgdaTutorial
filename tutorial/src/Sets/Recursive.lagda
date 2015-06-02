% Recursive Sets

Import List
===========

\begin{code}
module Sets.Recursive where

open import Data.Bool using (Bool; true; false)
\end{code}

The effect of this `open import` declaration is the same as if we copied the
definition of the `Bool` type here.  Note that we enumerated the constructors of
`Bool` too.

More about import declarations will come later.


Peano representation
============================

We are looking for a representation for the natural numbers.
The simplest choice is the *Peano representation* which corresponds to the
unary numeral system:

term                    interpretation in decimal form
----------------------- --------------------------
`zero`                  0
`suc zero`              1
`suc (suc zero)`        2
`suc (suc (suc zero))`  3
...                     ...


Definition of `ℕ`
==============

In Agda, the definition of natural numbers is as follows.

\begin{code}
data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ
\end{code}

Note that this definition yields the infinite set of judgements.

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


Type checking of expressions
=======================

With the Emacs command C-`c` C-`d`, one can get Agda to type check
a given expression (`d` stands for 'deduce').

Example: Hit C-`c` C-`d` and enter `suc (suc zero)`.

Exercises
---------

Deduce the type of the following expressions with Agda:

-   `suc zero`
-   `suc (zero)`
-   `(suc) zero`
-   `zero suc`
-   `(suc suc) zero`
-   `suc`


Binary representation of `ℕ`
==============

Consider the following definition of positive natural numbers, labelled as ℕ⁺:

\begin{code}
data ℕ⁺ : Set where
  one      :      ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺
\end{code}

Note that this definition above yields the following judgements
(without ordering):

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


Soon we will prove in Agda that `ℕ` and `ℕ₂` are isomorphic with the following
relation:

**ℕ**                   **ℕ₂**
----------------------- --------------------------
`zero`                  `zero`
`suc zero`              `id one`
`suc (suc zero)`        `id (double one)`
`suc (suc (suc zero))`  `id (double+1 one)`
...                     ...

Exercises
---------

1. How 9 is represented in `ℕ₂`?  Type check that expression.

1. Why did not we simply use one `data` definition with 4 constructors,
   such as `zero`, `one`, `double`, and `double+1`?



Rationale behind different representations
==========================================

Each representation has its merit.

Exercise
--------

Determine which representation (`ℕ` or `ℕ₂`) is better for the following tasks.

 * Compute `n * 2`.
 * Compute `⌊n / 2⌋`.
 * Decide whether the number is odd.
 * Compute `n + m`.
 * Compute `n * m`.
 * Prove that `n + m` = `m + n` for all `m` and `n`.
 * Store a number.

*****************

A good strategy is to choose the right representation for each task
and convert values between different representations.


Exercise
--------

Define `ℤ`.

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


Exercise
--------

Define binary trees according to the following shapes.

![Binary tree shapes](dot/Binary_tree_shapes.gif)



Exercises
---------

1.  Define binary trees
    -   with natural number data attached to the leafs
    -   with natural number data attached to the nodes
    -   with Booleans in the nodes and natural numbers in the leafs

1.  Define the lists (finite sequences) of natural numbers.

1.  Define the non-empty lists of natural numbers.



