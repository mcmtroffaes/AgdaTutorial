% Universal Quantification


Imports
========

\begin{code}
module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)
\end{code}



Universal quantification
======

We can represent a proof for universal quantification on a set by
a dependent function on that set.

Example:

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
\end{code}

<!--
\begin{code}
≤-trans z≤n   n≤o       = z≤n --
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o) --
-- antisym   : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n  --
--   (we will only define this after we have defined equality)  --
\end{code}
-->

\begin{code}
total        : ∀ m n → m ≤ n ⊎ n ≤ m -- hint: use [_,_]′
\end{code}

<!--
\begin{code}
total zero    _       = inj₁ z≤n --
total _       zero    = inj₂ z≤n --
total (suc m) (suc n)  --
   = [_,_]′ --
       (λ m≤n → inj₁ (s≤s m≤n)) --
       (λ n≤m → inj₂ (s≤s n≤m)) --
       (total m n) --
\end{code}
-->

From the 4 above properties follows that `_≤_` is a total order on `ℕ`. (We can look at `_≤_` as a relation over `ℕ`.)

\begin{code}
≤-pred  : ∀ {m n} → suc m ≤ suc n → m ≤ n
\end{code}

<!--
\begin{code}
≤-pred (s≤s m≤n) = m≤n --
\end{code}
-->

\begin{code}
≤-mono  : ∀ {m n k} → n ≤ m → k + n ≤ k + m
\end{code}

<!--
\begin{code}
≤-mono {k = zero}  n≤m = n≤m --
≤-mono {k = suc k} n≤m = s≤s $ ≤-mono {k = k} n≤m --
\end{code}
-->

Exercises
=============

Define the following functions:

\begin{code}
≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
\end{code}

<!--
\begin{code}
≤-step z≤n   = z≤n --
≤-step (s≤s m≤n) = s≤s (≤-step m≤n) --
\end{code}
-->

\begin{code}
≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
\end{code}

<!--
\begin{code}
≤′⇒≤ ≤′-refl        = ≤-refl _ --
≤′⇒≤ (≤′-step m≤′n) = ≤-step $ ≤′⇒≤ m≤′n --
\end{code}
-->

\begin{code}
z≤′n : ∀ n → zero ≤′ n
\end{code}

<!--
\begin{code}
z≤′n zero  = ≤′-refl --
z≤′n (suc n) = ≤′-step (z≤′n _) --
\end{code}
-->

\begin{code}
s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
\end{code}

<!--
\begin{code}
s≤′s ≤′-refl        = ≤′-refl --
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n) --
\end{code}
-->

\begin{code}
≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
\end{code}

<!--
\begin{code}
≤⇒≤′ z≤n   = z≤′n _ --
≤⇒≤′ (s≤s a≤b) = s≤′s $ ≤⇒≤′ a≤b --
\end{code}
-->
