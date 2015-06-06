% Sets with Functions

\begin{code}
module Sets.With_Functions where

open import Data.Nat using (zero; suc; ℕ; _+_)
open import Data.Bool
open import Data.Empty using (⊥)
open import Data.List using (List; length; _∷_; [])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
\end{code}


Types with function application in indices
==========================================

Consider the following two types that are equivalent:

\begin{code}
data Even : ℕ → Set where
  double : ∀ n → Even (n + n)

data Even′ (m : ℕ) : Set where
  double : ∀ n → m ≡ n + n → Even′ m
\end{code}

There exist conversion functions between those types:

\begin{code}
toEven : ∀ {m} → Even′ m → Even m
toEven {.(n + n)} (double n refl) = double n

toEven′ : ∀ {m} → Even m → Even′ m
toEven′ {.(n + n)} (double n) = double n refl
\end{code}


Usage
=====

Although `Even` and `Even′` are equivalent, `Even′` is much easier to use.  In
order to see this, let us try to prove that `Even n` is decidable for all `n`.

The concept of "decidable" is modelled by the `Dec` set (we will discuss that
later, just take a quick look at its definition for now):

\begin{code}
infix 3 ¬_

¬_ : ∀ {A} → Set A → Set A
¬ P = P → ⊥

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
\end{code}

Lemmata
=======

Consider the following lemmata for the proofs:

\begin{code}
suc-+ : ∀ n m → suc (n + m) ≡ n + suc m
suc-+ zero    m = refl
suc-+ (suc n) m = cong suc (suc-+ n m)

prev-≡ : ∀ {n m} → suc n ≡ suc m → n ≡ m
prev-≡ {.m} {m} refl = refl
\end{code}

Proof for `Even′`
=================

With the help of the lemmata, the proof for `Even′` could be given as
follows.  Note the use of a new construct, the `with` keyword in the
function definitions.  This keyword is used to implement pattern matching
on the value of the recursive invocation.

\begin{code}
nextEven′ : ∀ {n} → Even′ n → Even′ (suc (suc n))
nextEven′ {.(n₁ + n₁)} (double n₁ refl)
  = double (suc n₁) (cong suc (suc-+ n₁ n₁))

prevEven′ : ∀ {n} → Even′ (suc (suc n)) → Even′ n
prevEven′ {m} (double zero ())
prevEven′ {m} (double (suc n) x)
  = double n (prev-≡ (trans (prev-≡ x) (sym (suc-+ n n))))

¬Even′1 : ¬ (Even′ 1)
¬Even′1 (double zero ())
¬Even′1 (double (suc zero) ())
¬Even′1 (double (suc (suc n)) ())

isEven′ : (n : ℕ) → Dec (Even′ n)
isEven′ zero       = yes (double zero refl)
isEven′ (suc zero) = no ¬Even′1
isEven′ (suc (suc n)) with (isEven′ n)
... | yes e = yes (nextEven′ e)
... | no ¬p = no (λ x → ¬p (prevEven′ x))
\end{code}

Just for the sake of comparison, here is an example of using `with` in a
regular function definition.

\begin{code}
filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with (p x)
... | true  = x ∷ filter p xs
... | false = filter p xs
\end{code}

The `rewrite` construct
=======================

If `x : a ≡ b`, it is also possible to write the following:

~~~~{.agda}
f params rewrite x = body
~~~~~

instead of that:

~~~~{.agda}
f params with a | x
... | ._ | refl = body
~~~~

The `rewrite` construct has the effect of rewriting the goal and the
context by the given equation (left to right).

The function can be rewritten with using several equations (in sequence)
by separating them with vertical bars (`|`):

~~~~{.agda}
f params rewrite x₁ | x₂ | … = body
~~~~

It is also possible to add with clauses after rewriting:

~~~~{.agda}
f params rewrite xs with x
... | p = body
~~~~

Note that pattern matching happens before rewriting.  If you want to
rewrite and then do pattern matching you can use a `with` after the
rewrite.

Proof for `Even`
================

Now try to construct the proof with using `Even`.  As part of this, we will
soon come to the conclusion that `¬Even1` is only possible to prove when a
trick is employed:

\begin{code}
¬Even1 : ∀ {n} → Even n → ¬ (n ≡ 1)
¬Even1 (double zero) ()
¬Even1 (double (suc zero)) ()
¬Even1 (double (suc (suc n))) ()
\end{code}

For proving `nextEven`,  we will need to do a rewriting (see above):

\begin{code}
nextEven : ∀ {n} → Even n → Even (suc (suc n))
nextEven {.(n₁ + n₁)} (double n₁) rewrite (cong suc (suc-+ n₁ n₁)) = double (suc n₁)
\end{code}

However, we could prove `prevEven` only with the help of `prevEven′` that
demonstrates that `Even′` is actually easier to use:

\begin{code}
prevEven : ∀ {n} → Even (suc (suc n)) → Even n
prevEven e = toEven (prevEven′ (toEven′ e))
\end{code}

Note that proving `isEven` is similar to proving `isEven′`:

\begin{code}
isEven : (n : ℕ) → Dec (Even n)
isEven zero       = yes (double zero)
isEven (suc zero) = no (λ x → ¬Even1 x refl)
isEven (suc (suc n)) with (isEven n)
... | yes e = yes (nextEven e)
... | no ¬p = no (λ x → ¬p (prevEven x))
\end{code}


Further examples
================

\begin{code}
data  _≤″_ : ℕ → ℕ → Set  where
   diff : ∀ i j → i ≤″ j + i

infix 4 _≤″_

data Vec (A : Set) : ℕ -> Set where
  vec : (x : List A) -> Vec A (length x)
\end{code}
