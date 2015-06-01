% Functions with Set Results


Import list
===========

\begin{code}
module Functions.Large where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
\end{code}

Introduction
============

Function definitions give another possibility to define sets.  Here we will
give general design guidelines on which language construct to use in certain
situations.

Inductive definition of `_≤_`
==========

Consider the *inductive* definition of `_≤_` as follows:

\begin{code}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}   →         zero  ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}

that will yield the following statements:

~~~~~~~~~~~~~~~~~
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
~~~~~~~~~~~~~~~~~

Recursive definition of `_≤_`
==========

In comparison, now consider the *recursive* definition of `_≤_` as follows
(written as `_≤′_`):

\begin{code}
_≤′_ : ℕ → ℕ → Set
zero  ≤′ n     = ⊤
suc m ≤′ zero  = ⊥
suc m ≤′ suc n = m ≤′ n
\end{code}

that will yield the following statements:

~~~~~~~~~~~~~~~~~
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
~~~~~~~~~~~~~~~~~


Inductive vs. recursive definitions
===============

`_≤_` and `_≤′_` have the same type and define exactly the same relations.  But
note that:

**Inductive definitions are better than recursive definitions with pattern
matching.**

Suppose that we have `n : ℕ`, `m : ℕ` in a function definition.

 - In case of `e : n ≤ m`, we *can* pattern match on `e` -- the possible cases
   are `z≤n` and `s≤s x`.

 - In case of `e : n ≤′ m`, we *cannot* pattern match on `e`, because the type
   of `e` is not yet known to be either `⊥` or `⊤`. We should pattern match on
   `n` and `m` before to we could learn more about `n ≤′ m`.

For example (we are going to discuss *dependent functions* like this one
later):

\begin{code}
f : {n m : ℕ} → n ≤ m → n ≤ suc m
f z≤n     = z≤n
f (s≤s x) = s≤s (f x)

f′ : {n m : ℕ} → n ≤′ m → n ≤′ suc m
f′ {zero}  {m}     tt = tt
f′ {suc n} {zero}  ()
f′ {suc n} {suc m} x  = f′ {n} {m} x
\end{code}

<!--
\begin{code}
conv : {n m : ℕ} → n ≤′ m → n ≤ m  --
conv {zero}         tt = z≤n  --
conv {suc n} {zero} ()  --
conv {suc n} {suc m} e = s≤s (conv e) --
\end{code}
-->

Exercises
---------

 #. Give recursive definitions for `_≡_` and `_≢_` on natural numbers.

 #. Give mutual recursive definitions for the `Even` and `Odd` sets.

<!--
\begin{code}
Even : ℕ → Set --
Odd : ℕ → Set --

Even zero = ⊤ --
Even (suc n) = Odd n --

Odd zero = ⊥ --
Odd (suc n) = Even n --
\end{code}
-->


Macro-like `Set` definitions
=================

We can create macro-like function definitions that do not pattern match on
their argument:

\begin{code}
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m
\end{code}

Although we could have an inductive definition of `_<_`, this definition is
better because no conversion functions are needed between `_≤_` and `_<_`.

On the other hand, while the following would be also possible:

\begin{code}
Maybe : Set → Set
Maybe A = ⊤ ⊎ A
\end{code}

in general, this is not advised because then we cannot distinguish
`Maybe ⊤` from `⊤ ⊎ ⊤`, for example.

We can summarize the general rule as follows:

**Macro-like `Set` definitions are better than inductive definitions if
we do not want to distinguish the new (derived) type from the base
type.**

Exercise
--------

Define `_>_` and `_≥_` on top of `_≤_`.

Another example
===============

A good example of the macro-like behavior is the definition of the `¬`
function.  This is used to create a shorthand for writing negated statements
(which we are also going to use later).

\begin{code}
¬ : Set → Set
¬ A = A → ⊥
\end{code}

Another example: recursive `Fin`
================================

Recall the definition of the `Fin` indexed type from earlier:

\begin{code}
data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)
\end{code}

With this in mind, consider the `Fin₀` function, where `Fin₀ n` is isomorphic
to `Fin n` for all `n`:

\begin{code}
Fin₀ : ℕ → Set
Fin₀ zero    = ⊥
Fin₀ (suc n) = ⊤ ⊎ Fin₀ n
\end{code}

Compare the produced elements:

    n    Fin₀ n                             Fin n
    ------------------------------------------------------------------
    0    {                              }   {                      }
    1    { inj₁ tt                      }   { zero                 }
    2    { inj₁ tt                          { zero
         , inj₂ (inj₁ tt)               }   , suc zero             }
    3    { inj₁ tt                          { zero
         , inj₂ (inj₁ tt)                   , suc zero
         , inj₂ (inj₂ (inj₁ tt)         }   , suc (suc zero)       }
    4    { inj₁ tt                          { zero
         , inj₂ (inj₁ tt)                   , suc zero
         , inj₂ (inj₂ (inj₁ tt))            , suc (suc zero)
         , inj₂ (inj₂ (inj₂ (inj₁ tt))) }   , suc (suc (suc zero)) }
    ...

Based on the table above, we can observe the following pattern:

 * `zero` ~ `inj₁ tt`
 * `suc` ~ `inj₂`



