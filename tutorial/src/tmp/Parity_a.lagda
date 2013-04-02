% Parity View
% Ambrus Kaposi
% 2011. 12. 01.

\begin{code}
module Parity_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Nat  using (ℕ; zero; suc; pred; _+_; _*_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Sum  using (_⊎_; inj₁; inj₂)
\end{code}


Parity View
===========

Predicates are sets with one (if a proof existed) or zero (if no proof existed) element. Views are sets with exactly one element.

\begin{code}
data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(k * 2))       | even k = odd k
parity (suc .(suc (k * 2))) | odd  k = even (1 + k)
\end{code}

`Parity` is a view on natural numbers expressing that every natural number is either even or odd.
`parity` is called the *view function* of `Parity` which proves that there is exactly one element for every value of the index of the view.

If we pattern match on `parity n` we learn not only whether `n` is even or odd but we also learn what the value of the corresponding `k` is.

Compare it with the following function:

\begin{code}
isEven : ℕ → Bool
isEven zero    = true
isEven (suc n) = not (isEven n)
\end{code}

Parity is a union of the `Even'` and `Odd'` predicates:

\begin{code}
data Even' : ℕ → Set where
  even : (k : ℕ) → Even' (k * 2)

data Odd' : ℕ → Set where
  odd : (k : ℕ) → Odd' (1 + k * 2)
\end{code}

*Exercise:* define the view function for this union predicate:

\begin{code}
parity' : (n : ℕ) → Even' n ⊎ Odd' n
parity' zero    = inj₁ (even 0) --
parity' (suc n) with parity' n --
parity' (suc .(k * 2))       | inj₁ (even k) = inj₂ (odd k) --
parity' (suc .(suc (k * 2))) | inj₂ (odd  k) = inj₁ (even (suc k)) --
\end{code}

*Question:* what is the exact definition of the view that this view function gives? (Hint: use `Σ`.)


Exercises
=========

Define a similar function to `parity'` but for the original definitions of `Even` and `Odd`:

\begin{code}
data Even : ℕ → Set where
  z  : Even zero
  ss : {n : ℕ} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  o  : Odd (suc zero)
  ss : {n : ℕ} → Odd n → Odd (suc (suc n))

odd+1    : {n : ℕ} → Odd  n → Even (suc n)
odd+1 o      = ss z
odd+1 (ss n) = ss (odd+1 n)
even+1   : {n : ℕ} → Even n → Odd (suc n)
even+1 z      = o
even+1 (ss n) = ss (even+1 n)

parity2 : (n : ℕ) → Even n ⊎ Odd n
parity2 zero    = inj₁ z --
parity2 (suc n) with parity2 n --
parity2 (suc n) | inj₁ pe = inj₂ (even+1 pe) --
parity2 (suc n) | inj₂ po = inj₁ (odd+1  po) --
\end{code}

`parity2` gives a probably less useful proof on the parity of the number (because `Even` and `Odd` were originally not very useful).

Define division by 2 with the help of `Parity`:

\begin{code}
⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
⌊ n /2⌋ with parity n --
⌊ .(k * 2) /2⌋       | even k = k --
⌊ .(suc (k * 2)) /2⌋ | odd  k = k --
\end{code}

Define congruence classes of 4 as a view on natural numbers! Hint: use `Parity` when implementing the view function.
