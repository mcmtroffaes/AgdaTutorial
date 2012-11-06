% Proofs
% Péter Diviánszky and Ambrus Kaposi
% 2011. 05. 03.


Imports
========

\begin{code}
module Proofs_a where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)
\end{code}


Dependently typed functions
===============

Dependently typed function:

`f : (x : A) → B`, where `B` may depend on `x`

*Example*  
Let `Fin n` be the set of natural numbers less than `n`.  
`a : (n : ℕ) → Fin n` is a sequence whose `n`th elem is in `Fin n`.

*Notes*


-   Polymorph functions like `(A : Set) → A → A` are also dependent functions.
-   Non-dependent functions like `A → B` are special `(x : A) → B` functions where `B`
    doesn't depend on `x`.
-   ∣`(x : A)→ B`∣ = ∏`x`∈`A` ∣`B`∣, for example  
    ∣`(n : Fin m)→ Fin (suc n)`∣ = (`m` + 1)!


Definition of `_≤_`
===================

Remember

\begin{code}
data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →               zero  ≤ n
  s≤s : {m n : ℕ} →   m ≤ n  →  suc m ≤ suc n

infix 4 _≤_
\end{code}


Proof example
======


\begin{code}
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)
\end{code}

Exercises
=========

Define the following functions (prove these properties):

\begin{code}
≤-trans      : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n   n≤o       = z≤n --
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o) --
-- antisym   : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n  --
--   (we will only define this after we have defined equality)  --

total        : ∀ m n → m ≤ n ⊎ n ≤ m -- hint: use [_,_]′
total zero    _       = inj₁ z≤n --
total _       zero    = inj₂ z≤n --
total (suc m) (suc n)  --
   = [_,_]′ --
       (λ m≤n → inj₁ (s≤s m≤n)) --
       (λ n≤m → inj₂ (s≤s n≤m)) --
       (total m n) --
\end{code}

From the 4 above properties follows that `_≤_` is a total order on `ℕ`. (We can look at `_≤_` as a relation over `ℕ`.)

\begin{code}
≤-pred  : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n --

≤-mono  : ∀ {m n k} → n ≤ m → k + n ≤ k + m
≤-mono {k = zero}  n≤m = n≤m --
≤-mono {k = suc k} n≤m = s≤s $ ≤-mono {k = k} n≤m --
\end{code}


Exercises
=============

Recall

\begin{code}
data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                    m ≤′ m
  ≤′-step : {n : ℕ} → m ≤′ n → m ≤′ suc n

infix 4 _≤′_
\end{code}

Define the following functions:

\begin{code}
≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n   = z≤n --
≤-step (s≤s m≤n) = s≤s (≤-step m≤n) --

≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
≤′⇒≤ ≤′-refl        = ≤-refl _ --
≤′⇒≤ (≤′-step m≤′n) = ≤-step $ ≤′⇒≤ m≤′n --

z≤′n : ∀ n → zero ≤′ n
z≤′n zero  = ≤′-refl --
z≤′n (suc n) = ≤′-step (z≤′n _) --

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl        = ≤′-refl --
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n) --

≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
≤⇒≤′ z≤n   = z≤′n _ --
≤⇒≤′ (s≤s a≤b) = s≤′s $ ≤⇒≤′ a≤b --
\end{code}

