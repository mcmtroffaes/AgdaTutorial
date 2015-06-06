% Decidability View

\begin{code}
module Functions.Views.Decidability where
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


Definition
==========

The *decidability view* is a view on `Set`, a function
with type `(A : Set) → A ⊎ ¬ A`.


Individual constructors
=======================

`A ⊎ ¬ A`  ~  `Dec A`  where

\begin{code}
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
\end{code}



Discussion
==========

In Agda the decidability view can only be postulated, it
cannot be defined.  

We do not want to work with postulates, so define the
decidability view on the "classical fragment" of `Set`, case-by-case.


Exercises
=========

Define the decidability view for `1 < 2`, `1 ≡ 1`, `1 ≡ 2` and `1 > 2`:

\begin{code}
1<2 : Dec (1 < 2)
\end{code}

<!--
\begin{code}
1<2 = yes (s≤s (s≤s z≤n))
\end{code}
-->

\begin{code}
1≡1 : Dec (1 ≡ 1)
\end{code}

<!--
\begin{code}
1≡1 = yes refl
\end{code}
-->

\begin{code}
1≡2 : Dec (1 ≡ 2)
\end{code}

<!--
\begin{code}
1≡2 = no (λ ())
\end{code}
-->

\begin{code}
1>2 : Dec (1 > 2)
\end{code}

<!--
\begin{code}
1>2 = no f where
  f : ¬ (1 > 2)
  f (s≤s ())
\end{code}
-->


Exercises
=========

Define the decidability view for `n ≡ m` and `n ≤ m` where `n m : ℕ`:

\begin{code}
_≟_ : (a b : ℕ) → Dec (a ≡ b)
\end{code}

<!--
\begin{code}
zero  ≟ zero  = yes refl
zero  ≟ suc n = no (λ ())
suc n ≟ zero  = no (λ ())
suc n ≟ suc m with n ≟ m
suc n ≟ suc m | yes p = yes $ cong suc p
suc n ≟ suc m | no  p = no (help-≟ p)  where
  help-≟ : {n m : ℕ} → (n ≡ m → ⊥) → suc n ≡ suc m → ⊥
  help-≟ p refl = p refl
\end{code}
-->

\begin{code}
_≤?_ : (a b : ℕ) → Dec (a ≤ b)
\end{code}

<!--
\begin{code}
zero  ≤? _     = yes z≤n
suc _ ≤? zero  = no (λ ())
suc n ≤? suc m with n ≤? m
suc n ≤? suc m | yes p = yes (s≤s p)
suc n ≤? suc m | no  p = no $ help-≤? p  where
  help-≤? : {n m : ℕ} → (n ≤ m → ⊥) → suc n ≤ suc m → ⊥
  help-≤? p (s≤s q) = p q
\end{code}
-->


Usage of the decidability view
==============================

-   The decidability view turns Agda into a *classical* environment
    (otherwise it is constructive).

-   `Dec P` can be seen as an extended Boolean value as the following
    function shows:

\begin{code}
⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false
\end{code}


