% Addition predicate on ℕ
% Péter Diviánszky
% 2012. 09. 17.


Imports
========

\begin{code}
module Addition_a where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
\end{code}
| open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
| open import Function using (flip; _$_; _∘_)


`_+_≡_`: Addition predicate
==========

We wish to give a definition which
yields the infinite set of statements

~~~~~~~~~~~~~~~~~ {.haskell}
0 + 0 ≡ 0,  1 + 0 ≡ 1,  2 + 0 ≡ 2,  ...
0 + 1 ≡ 1,  1 + 1 ≡ 2,  2 + 1 ≡ 3,  ...
0 + 2 ≡ 2,  1 + 2 ≡ 3,  2 + 2 ≡ 4,  ...
...
~~~~~~~~~~~~~~~~~


The outline of the solution:

~~~~~~~~~~~~~~~~~ {.haskell}
(n : ℕ)                        zero  + n ≡ n     -- yields the first column of statements
(m : ℕ) (n : ℕ)  m + n ≡ k  →  suc m + n ≡ suc k -- yields the successive columns of statements
~~~~~~~~~~~~~~~~~

Technical details of the solution  
(nothing new but better to repeat):

*   We define the *set* `n + m ≡ k` for each `n : ℕ`, `m : ℕ` and `k : ℕ`.  
    (`2 + 2 ≡ 5` is a valid set too.)
*   The set `n + m ≡ k` will be non-empty iff `n` + `m` = `k`.  
    (`2 + 2 ≡ 4` is non-empty, `2 + 2 ≡ 5` is empty.)



Definition of `_+_≡_`
==========

`_+_̄≡_` is an indexed set with three natural number indices and with two constructors:*

\begin{code}
data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k
\end{code}

which yields the statements

~~~~~~~ {.haskell}
znn : 0 + 0 ≡ 0
znn : 0 + 1 ≡ 1
znn : 0 + 2 ≡ 2
...
sns znn : 1 + 0 ≡ 1
sns znn : 1 + 1 ≡ 2
sns znn : 1 + 2 ≡ 3
...
sns (sns znn) : 2 + 0 ≡ 2
sns (sns znn) : 2 + 1 ≡ 3
sns (sns znn) : 2 + 2 ≡ 4
...
...
~~~~~~~

Notes

*   Underscores in `_+_≡_` denote the space for the operands (mixfix notation).


*******************

*this is the same as

~~~~~~~ {.haskell}
data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : {n : ℕ} → zero + n ≡ n
  sns : {m : ℕ} → {n : ℕ} → m + n ≡ k → suc m + n ≡ suc k
~~~~~~~

Exercises
========

*   Prove that 5 + 5 = 10!
*   Prove that 2 + 2 ≠ 5!

\begin{code}
5+5≡10 : 5 + 5 ≡ 10  --
5+5≡10 = sns (sns (sns (sns (sns znn))))  --

2+2≢5 : 2 + 2 ≡ 5 → ⊥ --
2+2≢5 (sns (sns ())) --
\end{code}


Exercises
=========

*   Define `_⊓_ : ℕ → ℕ → Set` such that `n ⊓ m ≡ k` iff `k` is the minimum of `n` and `m`!
    *   Prove that `3 ⊓ 5 ≡ 3` is non-empty!
    *   Prove that `3 ⊓ 5 ≡ 5` is empty!
*   Define `_⊔_ : ℕ → ℕ → Set` such that `n ⊔ m ≡ k` iff `k` is the maximum of `n` and `m`!
    *   Prove that `3 ⊔ 5 ≡ 5` is non-empty!
    *   Prove that `3 ⊔ 5 ≡ 3` is empty!



Definition reuse
================

Another definition of `_≤_`:

\begin{code}
data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k
\end{code}

which yields

~~~~~~~~~ {.haskell}
≤+ znn : 0 ≤″ 0
≤+ znn : 0 ≤″ 1
≤+ znn : 0 ≤″ 2
...
≤+ (sns znn) : 1 ≤″ 1
≤+ (sns znn) : 1 ≤″ 2
≤+ (sns znn) : 1 ≤″ 3
...
≤+ (sns (sns znn)) : 2 ≤″ 2
≤+ (sns (sns znn)) : 2 ≤″ 3
≤+ (sns (sns znn)) : 2 ≤″ 4
...
...
~~~~~~~~~

Notes

 * This representation of less-than-or-equal is similar to `_≤_`.
 * If we write `≤+ : ∀ {m n k} → m + n ≡ k → n ≤″ k` (use `n` instead of `m` at the end) we get a representation of less-than-or-equal similar to `_≤′_` on the previous slides.


Exercises
=========

*   Define `_isDoubleOf_ : ℕ → ℕ → Set` on top of `_+_≡_`!
    *   Prove that `8 isDoubleOf 4` is non-empty!
    *   Prove that `9 isDoubleOf 4` is empty!
*   Define `_*_≡_ : ℕ → ℕ → Set` with the help of `_+_≡_`!
    *   Prove that `3 * 3 ≡ 9` is non-empty!
    *   Prove that `3 * 3 ≡ 8` is empty!
*   Define `_≈_ : ℕ → ℕ⁺ → Set` which represents the (canonical) isomorphism between `ℕ` and `ℕ⁺`!*
    *   Prove that `5 ≈ double+1 (double one)` is non-empty!
    *   Prove that `4 ≈ double+1 (double one)` is empty!

\begin{code}
data ℕ⁺ : Set where  --
  one    : ℕ⁺  --
  double : ℕ⁺ → ℕ⁺ --
  double+1 : ℕ⁺ → ℕ⁺ --

module ℕ≈ℕ⁺ where --

  data _≈_ : ℕ → ℕ⁺ → Set where --
    one : suc zero ≈ one --
    double : ∀ {k 2k m} → k + k ≡ 2k → k ≈ m → 2k ≈ double m  --
    +1 : ∀ {n m} →  n ≈ double m  →  suc n ≈ double+1 m --

  5≈5 : 5 ≈ double+1 (double one) --
  5≈5 = +1 (double (sns (sns znn)) (double (sns znn) one)) --

  4≉5 : 4 ≈ double+1 (double one)  → ⊥ --
  4≉5 (+1 (double (sns (sns (sns ()))) y)) --
\end{code}

*****************

*There are lots of isomorphism between `ℕ` and `ℕ⁺`, we mean here the most natural one.


