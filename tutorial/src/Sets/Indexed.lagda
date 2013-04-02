% Indexed Sets
% Péter Diviánszky
% 2013. 01.

Imports
=======

\begin{code}
module Sets.Indexed where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)
\end{code}


`Fin`, family of finite sets
===========

We wish to define a `ℕ`-indexed family of sets `Fin` such
that `Fin n` has exactly `n` elements.

Given the definition of `Fin`, the following equivalences would hold:

n   Sets with n elements
--- ---------------------------------
0   `Fin 0` ~ `⊥`
1   `Fin 1` ~ `⊤` ~ `Maybe ⊥` ~ `⊤ ⊎ ⊥`
2   `Fin 2` ~ `Bool` ~ `Maybe ⊤` ~ `Maybe (Maybe ⊥)` ~ `⊤ ⊎ ⊤ ⊎ ⊥`
3   `Fin 3` ~ `Maybe Bool` ~ `Maybe (Maybe (Maybe ⊥))` ~ `⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊥`
4   `Fin 4` ~ `Maybe (Maybe (Maybe (Maybe ⊥)))` ~ `⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊥`
... ...
--- ---------------------------------


Definition of `Fin`
==========

`Fin` is a set *indexed with* a natural number  
(we use `Fin` because this is not the final definition of `Fin`):

\begin{code}
data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)
\end{code}

The definition yields the statements

~~~~~~~~~~~~~~~~~ 
zero 0 : Fin 1
zero 1 : Fin 2
zero 2 : Fin 3
...
suc 1 (zero 0) : Fin 2
suc 2 (zero 1) : Fin 3
suc 3 (zero 2) : Fin 4
...
suc 2 (suc 1 (zero 0)) : Fin 3
suc 3 (suc 2 (zero 1)) : Fin 4
suc 4 (suc 3 (zero 2)) : Fin 5
...
...
~~~~~~~~~~~~~~~~~

which can be rearranged as

~~~~~~~~~~~~~~~~~ 
zero 0 : Fin 1

zero 1 : Fin 2
suc 1 (zero 0) : Fin 2

zero 2 : Fin 3
suc 2 (zero 1) : Fin 3
suc 2 (suc 1 (zero 0)) : Fin 3

zero 3 : Fin 4
suc 3 (zero 2) : Fin 4
suc 3 (suc 2 (zero 1)) : Fin 4
suc 3 (suc 2 (suc 1 (zero 0))) : Fin 4

...
~~~~~~~~~~~~~~~~~

So we can conclude that `Fin n` has `n` distinct elements.


Exercises
=========

*   Define a `Bool` indexed family of sets such that the set indexed by `false` contains
    no elements and the set indexed by `true` contains one element!
*   Define a `ℕ` indexed family of sets such that the sets indexed by even numbers contain
    one element and the others are empty!

<!--
\begin{code}
data So : Bool → Set where  --
  oh : So true --

data Even : ℕ → Set where --
  z : Even 0 --
  ss : (n : ℕ) → Even n → Even (suc (suc n)) --
\end{code}
-->


`Vec A n` ~ `A`^`n`^
==========

`Vec A n` is an `n`-tuple of elements of `A`:

\begin{code}
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)
\end{code}

Examples:

~~~~~~~~~~~~~~~~~ 
[] : Vec ℕ 0
[] : Vec Bool 0
...

cons 0 true [] : Vec Bool 1
...

cons 1 false (cons 0 true []) : Vec Bool 2
...
...
~~~~~~~~~~~~~~~~~


Exercise
========

*   Define a `Bool` indexed family of sets with two parameters, `A` and `B`, such
    that the set indexed by `false` contains
    an `A` element and the set indexed by `true` contains a `B` element!

<!--
\begin{code}
data Union (A B : Set) : Bool → Set where  --
  inj₁ : A → Union A B false --
  inj₂ : B → Union A B true --
\end{code}
-->

