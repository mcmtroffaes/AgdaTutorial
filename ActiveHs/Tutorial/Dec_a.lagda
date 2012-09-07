% Decidability View
% Ambrus Kaposi
% 2011. 12. 01.

\begin{code}
module Dec_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Nat   using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_)
open import Data.Bool  using (Bool; true; false; if_then_else_; not)
open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥)
open import Function   using (const; _$_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
\end{code}


Dec
===

\begin{code}
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
\end{code}

This is a view over decidable properties: `Dec A` has an element either if `A` is non-empty or `A` is provably empty.

*Exercise:* define the following functions:

\begin{code}
1<2 : Dec (1 < 2)
1<2 = yes (s≤s (s≤s z≤n)) --
1≡1 : Dec (1 ≡ 1)
1≡1 = yes refl --
1≡2 : Dec (1 ≡ 2)
1≡2 = no (λ ()) --
1>2 : Dec (1 > 2)
1>2 = no f where --
  f : ¬ (1 > 2) --
  f (s≤s ()) --
\end{code}

The view function has to be defined independently for each `A`.

*Exercise:* define the following view functions:

\begin{code}

help-≟ : {n m : ℕ} → (n ≡ m → ⊥) → suc n ≡ suc m → ⊥ --
help-≟ p refl = p refl --

_≟_ : (a b : ℕ) → Dec (a ≡ b)
zero  ≟ zero  = yes refl --
zero  ≟ suc n = no (λ ()) --
suc n ≟ zero  = no (λ ()) --
suc n ≟ suc m with n ≟ m --
suc n ≟ suc m | yes p = yes $ cong suc p --
suc n ≟ suc m | no  p = no (help-≟ p) --

{-
data _≤_ : Rel ℕ Level.zero where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
-}

help-≤? : {n m : ℕ} → (n ≤ m → ⊥) → suc n ≤ suc m → ⊥ --
help-≤? p (s≤s q) = p q --

_≤?_ : (a b : ℕ) → Dec (a ≤ b)
zero  ≤? _     = yes z≤n --
suc _ ≤? zero  = no (λ ()) --
suc n ≤? suc m with n ≤? m --
suc n ≤? suc m | yes p = yes (s≤s p) --
suc n ≤? suc m | no  p = no $ help-≤? p --
\end{code}

\begin{code}
T : Bool → Set
T true  = ⊤
T false = ⊥

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

True : {P : Set} → Dec P → Set
True Q = T ⌊ Q ⌋

False : {P : Set} → Dec P → Set
False Q = T (not ⌊ Q ⌋)

-- Gives a witness to the "truth".
toWitness : {P : Set} {Q : Dec P} → True Q → P
toWitness {Q = yes p} _  = p
toWitness {Q = no  _} ()

-- Establishes a "truth", given a witness.
fromWitness : {P : Set} {Q : Dec P} → P → True Q
fromWitness {Q = yes p} = const _
fromWitness {Q = no ¬p} = ¬p
\end{code}
