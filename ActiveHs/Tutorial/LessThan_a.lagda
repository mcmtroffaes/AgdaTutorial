% ≤ Predicate on ℕ
% Péter Diviánszky and Ambrus Kaposi
% 2011. 05. 03.

\begin{code}
module LessThan_a where
\end{code}


Motivation
===========

Let's define the following function:

`_≤?_ : ℕ → ℕ → Bool`

We call this a *question*. `n ≤ m` is `false` or `true` depending on the value of `n` and `m`. Booleans do not carry information about *what* and *why*.

Example of losing information when using a boolean:

\begin{code}
plus : ℕ → ℕ → ℕ
plus x y = if x ≤? zero then y else suc (plus (pred x) y)
\end{code}

| plus x y = case x of
|              zero  -> y
|              suc n -> suc (plus x y)
| 

*********************

More on "boolean blindness": [http://existentialtype.wordpress.com/2011/03/15/boolean-blindness](http://existentialtype.wordpress.com/2011/03/15/boolean-blindness)


Imports
========

\begin{code}
module Ordering where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)
\end{code}


`_≤_`: Less-Or-Equal Predicate
==========

`_≤_` is an *indexed* set with two natural number indices:

\begin{code}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : (n : ℕ)           → zero  ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_
\end{code}

`m ≤ n` has exactly one element if `m` less than or equal to `n`:

Set           1st,      2nd,            3rd,                   ...
------------- --------- --------------- ---------------------- ---
`0 ≤ 0` = {   `z≤n 0` }
`0 ≤ 1` = {   `z≤n 1` }
`0 ≤ 2` = {   `z≤n 2` }
...           ...       
`1 ≤ 0` = { } 
`1 ≤ 1` = {             `s≤s (z≤n 0)` }
`1 ≤ 2` = {             `s≤s (z≤n 1)` }
...                     ...             
`2 ≤ 0` = { } 
`2 ≤ 1` = { }
`2 ≤ 2` = {                             `s≤s (s≤s (z≤n 1))` }
...                                     ...                    
...           ...       ...             ...                    ...


`z≤n` and `s≤s` can be seen as the generators of the sets.


`_≤?_ : ℕ → ℕ → Bool` is a *question*. `n ≤ m` is `false` or `true`
depending on the value of `n` and `m`.

`_≤_ : ℕ → ℕ → Set` is a statement or *assertion*. If `q : n ≤ m` then
n ≤ m.


Exercise
==========

Define the following convenience functions:

\begin{code}
_<_ : ℕ → ℕ → Set
_≥_ : ℕ → ℕ → Set
_>_ : ℕ → ℕ → Set

infix 4 _<_ _≥_ _>_
\end{code}




Proofs
======

Define the following functions (prove these properties):

\begin{code}
≤-refl       : ∀ {n} → n ≤ n
| ≤-refl {zero}  = z≤n zero
| ≤-refl {suc n} = s≤s $ ≤-refl {n}
≤-trans      : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
| ≤-trans (z≤n _)   n≤o       = z≤n _
| ≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s $ ≤-trans m≤n n≤o
-- antisym   : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
--   (only after we defined equality)
total        : ∀ m n → m ≤ n ⊎ n ≤ m -- use [_,_]′
| total zero    _       = inj₁ $ z≤n _
| total _       zero    = inj₂ $ z≤n _
| total (suc m) (suc n) 
|    = [_,_]′
|        (λ m≤n → inj₁ (s≤s m≤n)) 
|        (λ n≤m → inj₂ (s≤s n≤m)) 
|        (total m n)
\end{code}

From the 4 above properties follows that `_≤_` is a total order on `ℕ`. (We can look at `_≤_` as a relation over `ℕ`.)

\begin{code}
≤-pred  : ∀ {m n} → suc m ≤ suc n → m ≤ n
| ≤-pred (s≤s m≤n) = m≤n
≤-mono  : ∀ {m n k} → n ≤ m → k + n ≤ k + m
| ≤-mono {k = zero}  n≤m = n≤m
| ≤-mono {k = suc k} n≤m = s≤s $ ≤-mono {k = k} n≤m

\end{code}


Alternative Definition
========

\begin{code}
data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                    m ≤′ m
  ≤′-step : {n : ℕ} → m ≤′ n → m ≤′ suc n

infix 4 _≤′_
\end{code}

Other alternative definition:

\begin{code}
data  _≤″_ : ℕ → ℕ → Set  where
   diff : (i j : ℕ) → i ≤″ j + i

infix 4 _≤″_
\end{code}

*Exercise:*

Explore the elements of sets `_≤′_` and `_≤″_`!


Rationale behind different definitions
======================================

*Exercise:*

Define the following functions:

\begin{code}
3≤5  : 3 ≤ 5
3≤′5 : 3 ≤′ 5
3≤″5 : 3 ≤″ 5

4≤4  : 4 ≤ 4
4≤′4 : 4 ≤′ 4
4≤″4 : 4 ≤″ 4
\end{code}


Define safe substraction:

\begin{code}
_∸_if_ : (a b : ℕ) → b ≤ a → ℕ
| zero ∸ .0     if z≤n .0       = 0
| suc a ∸ zero  if z≤n .(suc a) = suc a
| suc a ∸ suc b if s≤s p        = a ∸ b if p
\end{code}

Let's define it for the third version:

\begin{code}
_∸_if″_ : (a b : ℕ) → b ≤″ a → ℕ
| .(j + b) ∸ b if″ diff .b j = j
\end{code}



Exercises
=============

Define the following (helper and) conversion functions:

\begin{code}
≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
| ≤-step (z≤n _)   = z≤n (suc _)
| ≤-step (s≤s m≤n) = s≤s (≤-step m≤n)
≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
| ≤′⇒≤ ≤′-refl        = ≤-refl
| ≤′⇒≤ (≤′-step m≤′n) = ≤-step $ ≤′⇒≤ m≤′n

z≤′n : ∀ {n} → zero ≤′ n
| z≤′n {zero}  = ≤′-refl
| z≤′n {suc n} = ≤′-step z≤′n
s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
| s≤′s ≤′-refl        = ≤′-refl
| s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)
≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
| ≤⇒≤′ (z≤n _)   = z≤′n
| ≤⇒≤′ (s≤s a≤b) = s≤′s $ ≤⇒≤′ a≤b
\end{code}
