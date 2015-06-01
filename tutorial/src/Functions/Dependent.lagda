% Dependently Typed Functions

Import list
===========

\begin{code}
module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)
\end{code}


Dependently typed functions
===========================

We call the function `f : (x : A) → B` dependently-typed
if `B` (set) may depend on `x` (value).

For example, consider the following:

\begin{code}
fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero            -- Note: this is a different zero!
fromℕ (suc n) = suc (fromℕ n)
\end{code}

*Remarks:*

- The spaces of dependent functions are called `Π`-types because the number of
  their elements could be given as a product, that is:

    ∣ `(x : A) → B` ∣ = ∏(`x`∈`A`) ∣`B`∣

    For example:

    ∣ `(n : Fin m) → Fin (suc n)` ∣ = (`m` + 1)!

-   Polymorphic functions, such as `(A : Set) → A → A` are special cases for
    dependent functions.

-   Non-dependent functions, such as `A → B` are only special cases for dependent
    functions, that is:

    `(x : A) → B` where `B` does not depend on `x`, so it is `A → B`


Exercises
---------

1. Define a subtraction with a restricted domain.

     `_-_ : (n : ℕ) → Fin (suc n) → ℕ`

1. Define a conversion from `Fin n` to `ℕ`.

     `toℕ : ∀ {n} → Fin n → ℕ`

1. Define `fromℕ≤` such that `toℕ (fromℕ≤ e)` is `m` if `e : m < n`.

     `fromℕ≤ : ∀ {m n} → m < n → Fin n`

1. Define `inject+` such that `toℕ (inject+ n i)` is the same as `toℕ i`.

     `inject+ : ∀ {m} n → Fin m → Fin (m + n)`

1. Define `four` such that `toℕ four` is `4`:

     `four : Fin 66`

1. Define `raise` such that `toℕ (raise n i)` is the same as `n + toℕ i`:

     `raise : ∀ {m} n → Fin m → Fin (n + m)`

1. Define (a safe, total version of) `head` and `tail`.

     `head : ∀ {n}{A : Set} → Vec A (suc n) → A`  
     `tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n`

1. Define concatenation for vectors.

     `_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)`

1. Define `maps`. (Note that two cases will be enough.)

     `maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n`

1. Define `replicate`.

     `replicate : ∀ {n}{A : Set} → A → Vec A n`

1. Define `map` with the help of `maps` and `replicate`.

     `map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n`

1. Define `zip` with the help of `map` and `maps`.

     `zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n`

1. Define (safe, total) element indexing.

     `_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A`

<!--
\begin{code}
_-_ : (n : ℕ) → Fin (suc n) → ℕ
zero - zero = zero
zero - suc ()
suc n - zero = suc n
suc n - suc m = n - m

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = zero
toℕ (suc n) = suc (toℕ n)

fromℕ≤ : ∀ {m n} → m < n → Fin n
fromℕ≤ (s≤s z≤n)       = zero
fromℕ≤ (s≤s (s≤s m≤n)) = suc (fromℕ≤ (s≤s m≤n))

inject+ : ∀ {m} n → Fin m → Fin (m + n)
inject+ n zero    = zero
inject+ n (suc i) = suc (inject+ n i)

four : Fin 66
four = inject+ 61 (fromℕ 4)

raise : ∀ {m} n → Fin m → Fin (n + m)
raise zero i = i
raise (suc n) i = suc (raise n i)

head : ∀ {n}{A : Set} → Vec A (suc n) → A
head (a ∷ as) = a

tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
tail (a ∷ as) = as

_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = []
maps (f ∷ fs) (a ∷ as) = f a ∷ maps fs as

replicate : ∀ {n}{A : Set} → A → Vec A n
replicate {zero}  a = []
replicate {suc n} a = a ∷ replicate a

map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n
map f xs = maps (replicate f) xs

zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n
zip as bs = maps (map (_,_) as) bs

_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
[] ! ()
(a ∷ as) ! zero = a
(a ∷ as) ! suc n = as ! n
\end{code}
-->
