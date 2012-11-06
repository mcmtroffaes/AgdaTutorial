% Functions with Sets Result
% Péter Diviánszky
% 2012. 11. 06.


Imports
========

\begin{code}
module Large_a where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
\end{code}
| open import Function using (flip; _$_; _∘_)

Introduction
============

Function definitions give another possibility to define sets.  
We give general design rules which language construct to use.


Inductive `_≤_` definition
==========

The *inductive* definition of `_≤_`:

\begin{code}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →               zero  ≤ n
  s≤s : {m n : ℕ} →   m ≤ n  →  suc m ≤ suc n
\end{code}

which yields the statements

~~~~~~~~~~~~~~~~~ {.haskell}
z≤n : 0 ≤ 0
z≤n : 0 ≤ 1
z≤n : 0 ≤ 2
...
s≤s z≤n : 1 ≤ 1
s≤s z≤n : 1 ≤ 2
s≤s z≤n : 1 ≤ 3
...
s≤s (s≤s z≤n) : 2 ≤ 2
s≤s (s≤s z≤n) : 2 ≤ 3
s≤s (s≤s z≤n) : 2 ≤ 4
...
...
~~~~~~~~~~~~~~~~~


Recursive `_≤_` definition
==========

The *recursive* definition of less-than-or-equal:

\begin{code}
_≤′_ : ℕ → ℕ → Set
zero  ≤′ n     = ⊤
suc m ≤′ zero  = ⊥
suc m ≤′ suc n = m ≤′ n
\end{code}

which yields the statements

~~~~~~~~~~~~~~~~~ {.haskell}
tt : 0 ≤′ 0
tt : 0 ≤′ 1
tt : 0 ≤′ 2
...
tt : 1 ≤′ 1
tt : 1 ≤′ 2
tt : 1 ≤′ 3
...
tt : 2 ≤′ 2
tt : 2 ≤′ 3
tt : 2 ≤′ 4
...
...
~~~~~~~~~~~~~~~~~


Inductive vs. recursive definitions
===============

`_≤_` and `_≤′_` have the same type and define exatly the same relations. But:

**Inductive definitions are better than
recursive definitions with pattern matching.**

*Explanation*

Suppose in a function definition we have `n : ℕ`, `m : ℕ`.

-   In case of `e : n ≤ m` we *can* pattern match on `e`; the possible cases are `z≤n` and `s≤s x`.
-   In case of `e : n ≤′ m` we *cannot* pattern match on `e`, because the type of `e` is not yet known
    to be `⊥` or `⊤`. We should pattern match on `n` and `m` before to learn more about `n ≤′ m`.

Example (we discuss *dependent functions* like this later):

\begin{code}
f : {n m : ℕ} → n ≤ m → n ≤ suc m
f z≤n = z≤n
f (s≤s x) = s≤s (f x)

f′ : {n m : ℕ} → n ≤′ m → n ≤′ suc m
f′ {zero} {m} tt = tt
f′ {suc n} {zero} ()
f′ {suc n} {suc m} x = f′ {n} {m} x

conv : {n m : ℕ} → n ≤′ m → n ≤ m  --
conv {zero} tt = z≤n  --
conv {suc n} {zero} ()  --
conv {suc n} {suc m} e = s≤s (conv e) --
\end{code}


Exercises
========

Give recursive definitions for `_≡_` and `_≢_` on natural numbers!

Give mutual recursive definitions for `Even` and `Odd`!

\begin{code}
Even : ℕ → Set --
Odd : ℕ → Set --

Even zero = ⊤ --
Even (suc n) = Odd n --

Odd zero = ⊥ --
Odd (suc n) = Even n --
\end{code}



Macro-like `Set` definitions
=================

Macro-like functions don't pattern match on their argument:

\begin{code}
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m
\end{code}

Although we could have an inductive definition of `_<_`,
this definition is better because
no conversion functions needed between `_≤_` and `_<_`.

On the other hand,

\begin{code}
Maybe : Set → Set
Maybe A = ⊤ ⊎ A
\end{code}

is possible, but not advised because then we can't
distinguish `Maybe ⊤` from `⊤ ⊎ ⊤`, for example.

*General rule:*  
**Macro-like `Set` definitions are better than inductive definitions if
we don't want to distinguish the new type from the base type.**

Exercises
========

Define `_>_` and `_≥_` on top of `_≤_`!


Another example
===============

\begin{code}
¬ : Set → Set
¬ A = A → ⊥
\end{code}



