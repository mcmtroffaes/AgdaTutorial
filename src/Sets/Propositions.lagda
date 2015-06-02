% Propositions
% Péter Diviánszky and Ambrus Kaposi
% 2011. 05. 03., 2013. 01.


Import list
===========

\begin{code}
module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)
\end{code}


Proofs as data
==============

It is beneficial to represent proofs as ordinary data &mdash;
we can manipulate them like natural numbers.
The proofs of each proposition will have a distinct type.

We represent the proofs of the **true proposition** by the type `⊤`.
The true proposition has a trivial proof: `tt` (trivially true).

\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}

We represent the proofs of the **false proposition** by the type `⊥`.
False proposition have no proofs (thus they cannot be proven).

\begin{code}
data ⊥ : Set where
\end{code}

We represent the proofs of the **conjunction** of two propositions `A` and
`B` by the type `A × B`.  `A × B` has proofs of form `a , b` where `a` is a
proof of `A` and `b` is a proof of `B`.

\begin{code}
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_
\end{code}

We represent the proofs of the **disjunction** of two propositions `A` and
`B` by the type `A ⊎ B`.  `A ⊎ B` has two different kinds of proofs:

*   `inj₁ a`, where `a` is proof of `A`,
*   `inj₂ b`, where `b` is proof of `B`.

\begin{code}
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_
\end{code}


Exercises
=========

Construct one proof for each proposition if possible:  

-   `⊤ × ⊤`
-   `⊤ × ⊥`
-   `⊥ × ⊥`
-   `⊤ ⊎ ⊤`
-   `⊤ ⊎ ⊥`
-   `⊥ ⊎ ⊥`
-   `⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤`

For example:

\begin{code}
⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt
\end{code}


Remarks
=======

We will discuss the representation of implication, negation, universal, and
existential quantification later.

Note that `_⊎_` represents a *constructive* disjunction.  We are going to
formalize the classical disjunction that way and compare the obtained
concepts as we proceed.



`_≤_`: Less-or-equal predicate
==========

We wish to represent proofs of propositions n ≤ m (n, m = 0, 1, ...).  For this,
we define a set indexed with two natural numbers:

\begin{code}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                       zero  ≤ n
  s≤s : {m : ℕ} → {n : ℕ} →   m ≤ n  →  suc m ≤ suc n

infix 4 _≤_
\end{code}

This yields the following judgements:

~~~~~~~~~~~~~~~~~
z≤n {0} : 0 ≤ 0
z≤n {1} : 0 ≤ 1
z≤n {2} : 0 ≤ 2
...
s≤s (z≤n {0}) : 1 ≤ 1
s≤s (z≤n {1}) : 1 ≤ 2
s≤s (z≤n {2}) : 1 ≤ 3
...
s≤s (s≤s (z≤n {0})) : 2 ≤ 2
s≤s (s≤s (z≤n {1})) : 2 ≤ 3
s≤s (s≤s (z≤n {2})) : 2 ≤ 4
...
...
~~~~~~~~~~~~~~~~~

that means that the following propositions have proofs:

~~~~~~~~~~~~~~~~~
0 ≤ 0
0 ≤ 1,  1 ≤ 1
0 ≤ 2,  1 ≤ 2,  2 ≤ 2
0 ≤ 3,  1 ≤ 3,  2 ≤ 3,  3 ≤ 3
...                             ...
~~~~~~~~~~~~~~~~~


Notes:

*   The `z≤n` constructor yields the first column of judgements.
*   The `s≤s` constructor yields the successive columns of judgements.
*   `1 ≤ 0` is also a valid expression that denotes an empty set.


Proving non-emptiness
=====================

We can prove that a set is non-empty if we can construct any of its elements
(recall how constants may be defined):

\begin{code}
1≤10 : 1 ≤ 10
1≤10 = s≤s z≤n
\end{code}

Exercise
--------

Prove that 3 ≤ 7.

Proving emptiness
=================

How could we prove that a set like `7 ≤ 3` is empty?

1.  If `7 ≤ 3` was non-empty, all its elements would look like `s≤s x` where `x : 6 ≤ 2`.

    *   `z≤n` yields an element in `0 ≤ n` and `0` ≠ `7`.

1.  If `6 ≤ 2` was non-empty, all its elements would look like `s≤s x` where `x : 5 ≤ 1`.

    *   `z≤n` yields an element in `0 ≤ n` and `0` ≠ `6`.

1.  If `5 ≤ 1` was non-empty, all its elements would look like `s≤s x` where `x : 4 ≤ 0`.

    *   `z≤n` yields an element in `0 ≤ n` and `0` ≠ `5`.

1.  `4 ≤ 0` is empty.

    *   `z≤n` yields an element in `0 ≤ n` and `0` ≠ `4`.
    *   `s≤s` yields an element in `suc m ≤ suc n` and `suc n` ≠ `0`.

Although we will discuss all the details later, here we have a look at
how this chain of inference could be given in Agda:*

\begin{code}
7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))
\end{code}

where `()` denotes a value in a trivially empty set.

Exercise
--------

Prove that `4 ≤ 2` is empty.

Note that emptiness proofs can be used in other emptiness proofs:

\begin{code}
8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x
\end{code}

where `x` is an arbitrary variable name.

Exercise
--------

Guess what kind of code can be generated from emptiness proofs.


***************************

*: `7 ≤ 3 → ⊥` denotes a function from `7 ≤ 3` to `⊥` so we are proving that
`7 ≤ 3` is empty by giving a function that maps `7 ≤ 3` to a trivially empty
set.  Here, we show that `7 ≤ 3` has no elements hence the function is defined.
We are going to discuss functions in details later.


Exercises
---------

1.  Define an indexed set `_isDoubleOf_ : ℕ → ℕ → Set` such that `m isDoubleOf n`
    is non-empty iff (if and only if) `m` is the double of `n`.

    *   Prove that `8 isDoubleOf 4` is non-empty.
    *   Prove that `9 isDoubleOf 4` is empty.

1.  Define an indexed set `Odd : ℕ → Set` such that `Odd n` is non-empty iff `n`
    is odd.

    *   Prove that `Odd 9` is non-empty.
    *   Prove that `Odd 8` is empty.

1.  Define `Even : ℕ → Set` and `Odd : ℕ → Set` mutually.

1.  Define equality `_≡_ : ℕ → ℕ → Set`.

1.  Define non-equality `_≠_ : ℕ → ℕ → Set`.

<!--
| Equality on `ℕ`
| ===============
|
| \begin{code}
| data _≡₁_ : ℕ → ℕ → Set where --
|   zz : zero ≡₁ zero --
|   ss : {m n : ℕ} → m ≡₁ n → suc m ≡₁ suc n --
| 
| infix 4 _≡₁_ --
| \end{code}
| 
| yields
| 
| ~~~~~~~~~~~~~~~~~ 
| zz         : 0 ≡₁ 0
| ss zz      : 1 ≡₁ 1
| ss (ss zz) : 2 ≡₁ 2
| ...
| ~~~~~~~~~~~~~~~~~
|
| This is not isomorphic to ℕ.
| 
| *Exercises:*
| 
| Define the symmetry and transitivity of `_≡₁_`:
| 
| \begin{code}
| ≡₁-sym : ∀ {n m} → n ≡₁ m → m ≡₁ n
| ≡₁-sym zz = zz --
| ≡₁-sym (ss y) = ss (≡₁-sym y) --
| ≡₁-trans : ∀ a b c → a ≡₁ b → b ≡₁ c → a ≡₁ c
| ≡₁-trans .0 .0 c zz b≡c = b≡c --
| ≡₁-trans .(suc a) .(suc b) .(suc c) (ss {a} {b} a≡b) (ss {.b} {c} b≡c) = ss $ ≡₁-trans a b c a≡b b≡c --
| -- (reflexivity will be defined on next slide)
| \end{code}
| 
| Now we can define the antisymmetric property of `_≤_`:
| 
| \begin{code}
| antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡₁ n
| antisym z≤n z≤n = zz --
| antisym (s≤s m≤n) (s≤s n≤m) = ss $ antisym m≤n n≤m --
| \end{code}
| 
| \begin{code}
| data _≠_ : ℕ → ℕ → Set where --
|   z≠s : {n : ℕ}   →          zero ≠ suc n --
|   s≠z : {n : ℕ}   →         suc n ≠ zero --
|   s≠s : {m n : ℕ} → m ≠ n → suc m ≠ suc n --
| 
| data _isDoubleOf_ : ℕ → ℕ → Set where  --
|   z : zero isDoubleOf zero --
|   s : (m n : ℕ) → m isDoubleOf n → suc (suc m) isDoubleOf suc n --
| 
| 8isDoubleOf4 : 8 isDoubleOf 4 --
| 8isDoubleOf4 = s 6 3 (s 4 2 (s 2 1 (s 0 0 z))) --
| 
| 9isDoubleOf4 : 9 isDoubleOf 4 → ⊥ --
| 9isDoubleOf4 (s .7 .3 (s .5 .2 (s .3 .1 (s .1 .0 ()))))  --
| \end{code}
-->

Alternative representation of `_≤_`
========

Consider the following indexed type:

\begin{code}
data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n

infix 4 _≤′_
\end{code}

that yields the following:

~~~~~~~~~~~~~~~~~
≤′-refl : 0 ≤ 0
≤′-step ≤′-refl : 0 ≤ 1
≤′-step (≤′-step ≤′-refl) : 0 ≤ 2
...
≤′-refl : 1 ≤ 1
≤′-step ≤′-refl : 1 ≤ 2
≤′-step (≤′-step ≤′-refl) : 1 ≤ 3
...
≤′-refl : 2 ≤ 2
≤′-step ≤′-refl : 2 ≤ 3
≤′-step (≤′-step ≤′-refl) : 2 ≤ 4
...
...
~~~~~~~~~~~~~~~~~

As with `ℕ` and `ℕ₂`,

*   the structure of the `m ≤ n` and `m ≤′ n` set elements are different,
*   different representations are good for different tasks.

<!--
| Alternative Definition
| ========
| 
| \begin{code}
| data _≤′_ (m : ℕ) : ℕ → Set where
|   ≤′-refl :                    m ≤′ m
|   ≤′-step : {n : ℕ} → m ≤′ n → m ≤′ suc n
| 
| infix 4 _≤′_
| \end{code}
| 
| Other alternative definition:
| 
| \begin{code}
| data  _≤″_ : ℕ → ℕ → Set  where
|    diff : (i j : ℕ) → i ≤″ j + i
| 
| infix 4 _≤″_
| \end{code}
| 
| *Exercise:*
| 
| Explore the elements of sets `_≤′_` and `_≤″_`!
| 
| 
| Rationale behind different definitions
| ======================================
| 
| *Exercise:*
| 
| Define the following functions:
| 
| \begin{code}
| 3≤5  : 3 ≤ 5
| 3≤5 = s≤s (s≤s (s≤s (z≤n (suc (suc zero))))) --
| 3≤′5 : 3 ≤′ 5
| 3≤′5 = ≤′-step (≤′-step ≤′-refl) --
| 3≤″5 : 3 ≤″ 5
| 3≤″5 = diff (suc (suc (suc zero))) (suc (suc zero)) --
| 
| 4≤4  : 4 ≤ 4
| 4≤4 = s≤s (s≤s (s≤s (s≤s (z≤n zero)))) --
| 4≤′4 : 4 ≤′ 4
| 4≤′4 = ≤′-refl --
| 4≤″4 : 4 ≤″ 4
| 4≤″4 = diff (suc (suc (suc (suc zero)))) zero --
| \end{code}
| 
| 
| Define safe substraction:
| 
| \begin{code}
| _∸_if_ : (a b : ℕ) → b ≤ a → ℕ
| zero ∸ .0     if z≤n .0       = 0 --
| suc a ∸ zero  if z≤n .(suc a) = suc a --
| suc a ∸ suc b if s≤s p        = a ∸ b if p --
| \end{code}
| 
| Let's define it for the third version:
| 
| \begin{code}
| _∸_if″_ : (a b : ℕ) → b ≤″ a → ℕ
| .(j + b) ∸ b if″ diff .b j = j --
| \end{code}
| 
| 
| 
| Exercises
| =============
| 
| Define the following (helper and) conversion functions:
| 
| \begin{code}
| ≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
| ≤-step (z≤n _)   = z≤n (suc _) --
| ≤-step (s≤s m≤n) = s≤s (≤-step m≤n) --
| ≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
| ≤′⇒≤ ≤′-refl        = ≤-refl --
| ≤′⇒≤ (≤′-step m≤′n) = ≤-step $ ≤′⇒≤ m≤′n --
| 
| z≤′n : ∀ {n} → zero ≤′ n
| z≤′n {zero}  = ≤′-refl --
| z≤′n {suc n} = ≤′-step z≤′n --
| s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
| s≤′s ≤′-refl        = ≤′-refl --
| s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n) --
| ≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
| ≤⇒≤′ (z≤n _)   = z≤′n --
| ≤⇒≤′ (s≤s a≤b) = s≤′s $ ≤⇒≤′ a≤b --
| \end{code}
-->


Syntactic abbreviations
=======================

All code on this slide is valid.

Original definition:

~~~~~~~~~~~
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                       zero  ≤ n
  s≤s : {m : ℕ} → {n : ℕ} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

The arrows between typed variables are not needed (also in case of round parenthesis):

~~~~~~~~~~~
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                     zero  ≤ n
  s≤s : {m : ℕ} {n : ℕ} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

Typed variables with the same type can be merged (also in case of round parenthesis):

~~~~~~~~~~~
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →               zero  ≤ n
  s≤s : {m n : ℕ} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

Inferable expressions can be replaced by an underscore:

~~~~~~~~~~~
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : _} →               zero  ≤ n
  s≤s : {m n : _} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~

Variables with inferred types can be introduced by `∀`:

~~~~~~~~~~~
data  _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} →               zero  ≤ n
  s≤s : ∀ {m n} →   m ≤ n  →  suc m ≤ suc n
~~~~~~~~~~~


`_+_≡_`: Addition predicate
==========

We wish to give a definition that yields an infinite set of true propositions:

~~~~~~~~~~~~~~~~~
0 + 0 ≡ 0,  1 + 0 ≡ 1,  2 + 0 ≡ 2,  ...
0 + 1 ≡ 1,  1 + 1 ≡ 2,  2 + 1 ≡ 3,  ...
0 + 2 ≡ 2,  1 + 2 ≡ 3,  2 + 2 ≡ 4,  ...
...
~~~~~~~~~~~~~~~~~

The outline of the solution:

~~~~~~~~~~~~~~~~~
(n : ℕ)                        zero  + n ≡ n     -- yields the first column of judgements
(m : ℕ) (n : ℕ)  m + n ≡ k  →  suc m + n ≡ suc k -- yields the successive columns of judgements
~~~~~~~~~~~~~~~~~

Technical details of the solution (nothing new but better to repeat!):

*   We define the *set* `n + m ≡ k` for each `n : ℕ`, `m : ℕ` and `k : ℕ`.  
    (`2 + 2 ≡ 5` is a valid set too.)

*   The set `n + m ≡ k` will be non-empty iff `n` + `m` = `k`.  
    (`2 + 2 ≡ 4` is non-empty, `2 + 2 ≡ 5` is empty.)


Definition of `_+_≡_`
==========

`_+_≡_` is an indexed set with three natural number indices and two constructors:*

\begin{code}
data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k
\end{code}

that yields the following judgements:

~~~~~~~
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

Note that the underscores in `_+_≡_` denote the space for the operands
(i.e. mixfix notation).

*******************

*:  That is the same as follows:

~~~~~~~
data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : {n : ℕ} → zero + n ≡ n
  sns : {m : ℕ} → {n : ℕ} → {k : ℕ} → m + n ≡ k → suc m + n ≡ suc k
~~~~~~~

Exercises
---------

1. Prove that 5 + 5 = 10.

1. Prove that 2 + 2 ≠ 5.

1. Define `_⊓_≡_ : ℕ → ℕ → ℕ → Set` such that `m ⊓ n ≡ k` iff `k` is the minimum of
   `m` and `n`.

    *   Prove that both `3 ⊓ 5 ≡ 3` and `5 ⊓ 3 ≡ 3` are non-empty.
    *   Prove that `3 ⊓ 5 ≡ 5` is empty.

1. Define `_⊔_≡_ : ℕ → ℕ → ℕ → Set` such that `m ⊔ n ≡ k` iff `k` is the maximum of
   `m` and `n`.

    *   Prove that `3 ⊔ 5 ≡ 5` is non-empty.
    *   Prove that `3 ⊔ 5 ≡ 3` is empty.

<!--
\begin{code}
5+5≡10 : 5 + 5 ≡ 10  --
5+5≡10 = sns (sns (sns (sns (sns znn))))  --

2+2≢5 : 2 + 2 ≡ 5 → ⊥ --
2+2≢5 (sns (sns ())) --
\end{code}
-->

Reusing definitions
===================

Consider another definition of the `_≤_` type:

\begin{code}
data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k
\end{code}

that yields the following:

~~~~~~~~~
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

Notes:

 * This representation of less-than-or-equal is similar to `_≤_`.
 * If we were to wrote `≤+ : ∀ {m n k} → m + n ≡ k → n ≤″ k` (that is, use
   `n` instead of `m` at the end) we would get a representation of
   less-than-or-equal similar to `_≤′_` on the previous slides.


Exercises
---------

1.  Define `_isDoubleOf_ : ℕ → ℕ → Set` atop `_+_≡_`.

    *   Prove that `8 isDoubleOf 4` is non-empty.
    *   Prove that `9 isDoubleOf 4` is empty.

1.  Define `_*_≡_ : ℕ → ℕ → ℕ → Set` with the help of `_+_≡_`.

    *   Prove that `3 * 3 ≡ 9` is non-empty.
    *   Prove that `3 * 3 ≡ 8` is empty.

1.  Define `_≈_ : ℕ → ℕ⁺ → Set` that represents the (canonical) isomorphism
    between `ℕ` and `ℕ⁺`.*

    *   Prove that `5 ≈ double+1 (double one)` is non-empty.
    *   Prove that `4 ≈ double+1 (double one)` is empty.

*Hint.*  Recall the definition of `ℕ⁺`, `one`, `double`, `double+1`:

\begin{code}
data ℕ⁺ : Set where
  one      : ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺
\end{code}

<!--
\begin{code}
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
-->

*****************

*: There are many isomorphisms between `ℕ` and `ℕ⁺`, here we are referring to the
   most natural one.
