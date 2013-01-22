% Recursive Sets
% Péter Diviánszky
% 2011. 05. 03.

Import List
===========

\begin{code}
module Sets.Recursive where

open import Data.Bool using (Bool; true; false)
\end{code}

This opens and imports `Data.Bool` from the standard library. Without `open` we could only refer to the functions imported with qualified name such as `Data.Bool.bool`.


Peano representation
============================

We are looking for a representation natural numbers i.e.
a set which has as many elements as ℕ.  
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

yields the infinite set of statements

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

We may use `0`, `1`, `2`, ... instead of `zero`, `suc zero`, ...*

************************

*\ Decimal natural number literals can be used if we bind our `ℕ` set to the Agda internals with the following three declarations:

\begin{code}
-- {-# BUILTIN NATURAL ℕ    #-}
-- {-# BUILTIN ZERO    zero #-}
-- {-# BUILTIN SUC     suc  #-}
\end{code}


Set element definitions
=======================

\begin{code}
nine : ℕ
nine = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

ten : ℕ
ten = suc nine
\end{code}

The type signature is optional.




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

*Exercise:* define `nine : ℕ₂`!

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
and give the isomorphisms between the representations.


Exercises
=========

 * Define `ℤ`!
 * Define `ℚ`!

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


Infix notation
==============

\begin{code}
data BinTree' : Set where
  x : BinTree'
  _+_ : BinTree' → BinTree' → BinTree'
\end{code}

yields

~~~~~~~~~~~~~~~~~ 
BinTree' : Set
x : BinTree'
x + x : BinTree'
(x + x) + x : BinTree'
x + (x + x) : BinTree'
(x + x) + (x + x) : BinTree'
...
~~~~~~~~~~~~~~~~~

Underscores in names like `_+_` denote the space for the operands.  

One can give the precedence with `infix`, `infixl` or `infixr`:

\begin{code}
infixr 3 _+_
\end{code}

yields

~~~~~~~~~~~~~~~~~ 
BinTree' : Set
x : BinTree'
x + x : BinTree'
(x + x) + x : BinTree'
x + x + x : BinTree'
(x + x) + x + x : BinTree'
...
~~~~~~~~~~~~~~~~~

(so `_+_` has right precedence)


Exercises
=========

*   Define binary trees
    -   with natural number data attached to the leafs
    -   with natural number data attached to the nodes
    -   with Booleans in the nodes and natural numbers in the leafs
*   Define the lists of natural numbers! Use `_∷_` as list consructor with right precedence!
*   Define the non-empty lists of natural numbers!
*   Define trees with nodes with finite children (0, 1, 2, ...)!


Mutual definitions
=========


\begin{code}
mutual
  data L : Set where
    nil : L
    _∷_ : ℕ → M → L

  data M : Set where
    _∷_ : Bool → L → M
\end{code}

*Exercise*: What are the elements of `L` and `M`?


Exercise
=========

Define a small grammar!*

-------

*highly underspecified exercise


