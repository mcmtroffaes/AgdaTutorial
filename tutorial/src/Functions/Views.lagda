% Views

\begin{code}
module Functions.Views where

open import Data.Nat using (ℕ; zero; suc; _<_; _>_; s≤s; z≤n; _+_; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}


Definition
==========

Let `A` be a type.  
Let `P : A → Set` a disjunction (parameterized on `A`).

A *view on `A`* is a function with type `(a : A) → P a`.


Example
=======

Assume the following definitions.

\begin{code}
data Even : ℕ → Set
data Odd  : ℕ → Set

data Even where
  zero : Even zero
  odd  : ∀ {n} → Odd n → Even (suc n)

data Odd where
  even : ∀ {n} → Even n → Odd (suc n)
\end{code}

The parity view:

\begin{code}
parity : ∀ n → Even n ⊎ Odd n
parity zero = inj₁ zero
parity (suc n) with parity n
parity (suc n) | inj₁ x = inj₂ (even x)
parity (suc n) | inj₂ y = inj₁ (odd y)
\end{code}


Exercise
=======

The ordering view is a view on `ℕ × ℕ` (in curried form):

\begin{code}
ordering : ∀ n m →  n < m  ⊎  n ≡ m  ⊎  n > m
\end{code}

Define the ordering view!

<!--
\begin{code}
ordering zero zero = inj₂ (inj₁ refl)
ordering zero (suc m) = inj₁ (s≤s z≤n)
ordering (suc n) zero = inj₂ (inj₂ (s≤s z≤n))
ordering (suc n) (suc m) with ordering n m
ordering (suc n) (suc m)  | inj₁ x           = inj₁ (s≤s x)
ordering (suc n) (suc .n) | inj₂ (inj₁ refl) = inj₂ (inj₁ refl)
ordering (suc n) (suc m)  | inj₂ (inj₂ y)    = inj₂ (inj₂ (s≤s y))
\end{code}
-->


Individual constructors
=======================

The disjunction of the view can be replaced by an individual
data type:

`Even n ⊎ Odd n`  ~  `Parity n`  where

\begin{code}
data Parity : ℕ → Set where
  even : ∀ n → Parity (n * 2)
  odd  : ∀ n → Parity (1 + n * 2)
\end{code}

`n < m  ⊎  n ≡ m  ⊎  n > m`  ~  `Ordering n m`  where

\begin{code}
data Ordering : ℕ → ℕ → Set where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m
\end{code}


Exercises
=========

Define the functions

\begin{code}
parity′ : ∀ n → Parity n
\end{code}

<!--
\begin{code}
parity′ zero = even 0
parity′ (suc n) with parity′ n
parity′ (suc .(k * 2))     | even k = odd k
parity′ (suc .(1 + k * 2)) | odd  k = even (1 + k)
\end{code}
-->

\begin{code}
compare : ∀ m n → Ordering m n
\end{code}

<!--
\begin{code}
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k
\end{code}
-->


Usage of views
=====

If we pattern match on `parity n` we learn not only wether `n` is even or odd but we
also get a proof of it. From the proof we can get additional information too (like what is the
half of `n`).

Views are very handy with the `with` construct.


Exercises
=========

A) Define division by 2 with the help of `Parity`:

\begin{code}
⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
\end{code}

<!--
\begin{code}
⌊ n /2⌋ with parity′ n
⌊ .(k * 2) /2⌋       | even k = k
⌊ .(suc (k * 2)) /2⌋ | odd  k = k
\end{code}
-->

B) Define congruence classes of 4 as a view on natural numbers!  
Hint: use `Parity` when implementing the view function.
