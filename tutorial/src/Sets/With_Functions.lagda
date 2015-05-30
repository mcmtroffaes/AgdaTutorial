% Sets with Functions

\begin{code}
module Sets.With_Functions where

open import Data.Nat using (zero; suc; ℕ; _+_)
open import Data.Empty using (⊥)
open import Data.List using (List; length)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
\end{code}


Types with function application in indices
==========================================

The following two types are equivalent:

\begin{code}
data Even : ℕ → Set where
  double : ∀ n → Even (n + n)

data Even′ (m : ℕ) : Set where
  double : ∀ n → m ≡ n + n → Even′ m
\end{code}

Conversion functions:

\begin{code}
toEven : ∀ {m} → Even′ m → Even m
toEven {.(n + n)} (double n refl) = double n

toEven′ : ∀ {m} → Even m → Even′ m
toEven′ {.(n + n)} (double n) = double n refl
\end{code}


Usage
=====

Although `Even` and `Even′` are equivalent, `Even′` is much easier to use.

To see this, try to prove that `Even n` is decidable for all `n`.


Lemmas
======

\begin{code}
suc-+ : ∀ n m → suc (n + m) ≡ n + suc m
suc-+ zero m = refl
suc-+ (suc n) m = cong suc (suc-+ n m)

prev-≡ : ∀ {n m} → suc n ≡ suc m → n ≡ m
prev-≡ {.m} {m} refl = refl
\end{code}


Proof for `Even′`
======


\begin{code}
nextEven′ : ∀ {n} → Even′ n → Even′ (suc (suc n))
nextEven′ {.(n₁ + n₁)} (double n₁ refl)
    = double (suc n₁) (cong suc (suc-+ n₁ n₁))

prevEven′ : ∀ {n} → Even′ (suc (suc n)) → Even′ n
prevEven′ {m} (double zero ())
prevEven′ {m} (double (suc n) x)
    = double n (prev-≡ (trans (prev-≡ x) (sym (suc-+ n n))))

¬Even′1 : Even′ 1 → ⊥
¬Even′1 (double zero ())
¬Even′1 (double (suc zero) ())
¬Even′1 (double (suc (suc n)) ())

isEven′ : (n : ℕ) → Dec (Even′ n)
isEven′ zero = yes (double zero refl)
isEven′ (suc zero) = no ¬Even′1
isEven′ (suc (suc n)) with isEven′ n
isEven′ (suc (suc n)) | yes e = yes (nextEven′ e)
isEven′ (suc (suc n)) | no ¬p = no (λ x → ¬p (prevEven′ x))
\end{code}


Proof for `Even`
======

Now try to do the same for `Even`.

`¬Even1` is possible only with a trick:

\begin{code}
¬Even1 : ∀ {n} → Even n → n ≡ 1 → ⊥
¬Even1 (double zero) ()
¬Even1 (double (suc zero)) ()
¬Even1 (double (suc (suc n))) ()
\end{code}

For `nextEven` we need rewriting (a new feature):

\begin{code}
nextEven : ∀ {n} → Even n → Even (suc (suc n))
nextEven {.(n₁ + n₁)} (double n₁) rewrite cong suc (suc-+ n₁ n₁) = double (suc n₁)
\end{code}

However, I could prove `prevEven` only with the help of `prevEven′` which demonstrates
that `Even′` is easier to use:

\begin{code}
prevEven : ∀ {n} → Even (suc (suc n)) → Even n
prevEven e = toEven (prevEven′ (toEven′ e)) 
\end{code}

`isEven` is similar to `isEven′`:

\begin{code}
isEven : (n : ℕ) → Dec (Even n)
isEven zero = yes (double zero)
isEven (suc zero) = no (λ x → ¬Even1 x refl)
isEven (suc (suc n)) with isEven n
isEven (suc (suc n)) | yes e = yes (nextEven e)
isEven (suc (suc n)) | no ¬p = no (λ x → ¬p (prevEven x))
\end{code}


Other examples
==============

\begin{code}
data  _≤″_ : ℕ → ℕ → Set  where
   diff : ∀ i j → i ≤″ j + i

infix 4 _≤″_

data Vec (A : Set) : ℕ -> Set where
  vec : (x : List A) -> Vec A (length x)
\end{code}
