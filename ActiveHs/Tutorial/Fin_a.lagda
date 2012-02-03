% Finite Sets
% Ambrus Kaposi
% 2011. 10. 27.

\begin{code}
module Fin_a where
\end{code}


Imports
=======

\begin{code}
open import Data.Empty    using (⊥)
open import Data.Nat      using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _<′_; _≤′_; ≤′-refl; ≤′-step; _+_)
open import Data.Nat.Properties using (s≤′s)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Unit     using (⊤; tt)
open import Data.Vec      using (Vec; []; _∷_)
open import Function      using (_$_; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
\end{code}


Motivation
===========

Examples that we've seen so far:

    n   Set of n     (Set of n
        elements      elements)'
    -------------------------------------
    0   ⊥            ⊥
    1   ⊤            ⊤ ⊎ ⊥
    2   Bool         ⊤ ⊎ ⊤ ⊎ ⊥
    3   Maybe Bool   ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊥
    4                ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊥
    ...

Let's implement this:

\begin{code}
Fin₀ : ℕ → Set
Fin₀ zero    = ⊥
Fin₀ (suc n) = ⊤ ⊎ Fin₀ n
\end{code}

Elements:

    n    Fin₀ n
    -----------------------------------------
    0    {                                }
    1    {   inj₁ tt                      }
    2    {   inj₁ tt
           , inj₂ (inj₁ tt)               }
    3    {   inj₁ tt
           , inj₂ (inj₁ tt)
           , inj₂ (inj₂ (inj₁ tt)         }
    4    {   inj₁ tt
           , inj₂ (inj₁ tt)
           , inj₂ (inj₂ (inj₁ tt))
           , inj₂ (inj₂ (inj₂ (inj₁ tt))) }
    ...



Definition
==========

\begin{code}
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
\end{code}

Elements:

    n    Fin₀ n                             Fin n
    ------------------------------------------------------------------
    0    {                              }   {                      }
    1    { inj₁ tt                      }   { zero                 }
    2    { inj₁ tt                          { zero
         , inj₂ (inj₁ tt)               }   , suc zero             }
    3    { inj₁ tt                          { zero
         , inj₂ (inj₁ tt)                   , suc zero
         , inj₂ (inj₂ (inj₁ tt)         }   , suc (suc zero)       }
    4    { inj₁ tt                          { zero
         , inj₂ (inj₁ tt)                   , suc zero
         , inj₂ (inj₂ (inj₁ tt))            , suc (suc zero)
         , inj₂ (inj₂ (inj₂ (inj₁ tt))) }   , suc (suc (suc zero)) }
    ...

Pattern:

 * `zero` ~ `inj₁ tt`
 * `suc` ~ `inj₂`


Exercises
=========

Define a substraction with restricted domain:

\begin{code}
_-_ : (n : ℕ) → Fin (suc n) → ℕ
| zero - ()
| suc n - zero = suc n
| suc n - suc m = n - m
\end{code}

Define the following functions:

\begin{code}
toℕ : ∀ {n} → Fin n → ℕ
| toℕ zero    = zero
| toℕ (suc n) = suc (toℕ n)

fromℕ : (n : ℕ) → Fin (suc n)
| fromℕ zero = zero
| fromℕ (suc n) = suc (fromℕ n)

fromℕ≤ : ∀ {m n} → m < n → Fin n
| fromℕ≤ (s≤s z≤n)       = zero
| fromℕ≤ (s≤s (s≤s m≤n)) = suc (fromℕ≤ (s≤s m≤n))

to∘from : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n -- converting twice is id
| to∘from zero    = refl
| to∘from (suc n) = cong suc (to∘from n)

typSuc : ∀ {n} → Fin n → Fin (suc n)
| typSuc zero = zero
| typSuc (suc n) = suc (typSuc n)

raise : ∀ {m} n → Fin m → Fin (n + m)
| raise zero i = i
| raise (suc n) i = suc (raise n i)

four : Fin 5
| four = suc (suc (suc (suc zero)))

four' : Fin 6
| four' = typSuc four

four'' : Fin 66
| four'' = raise 61 four

\end{code}

More exercises
==============

\begin{code}
fin≤ : ∀ {n}(m : Fin n) → (toℕ m) < n
| fin≤ zero    = s≤s z≤n
| fin≤ (suc m) = s≤s (fin≤ m)

lemm : ∀ {n}(m : Fin n) → fromℕ≤ (fin≤ m) ≡ m → fromℕ≤ (s≤s (fin≤ m)) ≡ suc m
| lemm zero    p = refl
| lemm (suc m) p = cong suc p

from∘to : ∀ {n} (m : Fin n) → fromℕ≤ {toℕ m} {n} (fin≤ m) ≡ m
| from∘to zero    = refl
| from∘to (suc m) = lemm m (from∘to m)

fromℕ≤′ : ∀ {m n : ℕ} → m <′ n → Fin n -- use typSuc
| fromℕ≤′ {m} ≤′-refl = fromℕ m
| fromℕ≤′ (≤′-step m≤′n) = typSuc (fromℕ≤′ m≤′n)

fin≤′ : ∀ {n : ℕ}(m : Fin n) → (toℕ m) <′ n -- hint: use s≤′s
| fin≤′ (zero {zero})  = ≤′-refl
| fin≤′ (zero {suc n}) = ≤′-step $ fin≤′ zero 
| fin≤′ (suc {n} m)    = s≤′s $ fin≤′ m

from∘to′ : ∀ {n} (m : Fin n) → fromℕ≤′ {toℕ m} {n} (fin≤′ m) ≡ m
| from∘to′ (zero {zero}) = refl
| from∘to′ (zero {suc n}) = {!from∘to′ (zero {n})!}
| from∘to′ (suc m) = {!!}
| TODO
\end{code}


Alternative definition
======================

Now we can define indexing into vectors nicer (compare it with `_!_[_]` for `Vec`):

\begin{code}
_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
[] ! ()
(a ∷ as) ! zero = a
(a ∷ as) ! suc n = as ! n
\end{code}

This leads us to an alternative definition of `Fin`:

\begin{code}
data Fin' : ℕ -> Set where
  _,_ : ∀ {n} (i : ℕ) -> i < n -> Fin' n
\end{code}

Define this alternative version:

\begin{code}
_!'_ : ∀ {n}{A : Set} → Vec A n → Fin' n → A
| [] !' (_ , ())
| (a ∷ as) !' (zero  , _)     = a
| (a ∷ as) !' (suc n , s≤s p) = as !' (n , p)
\end{code}

Remember the following:

\begin{code}
_!_[_] : ∀ {n}{A : Set} → Vec A n → (m : ℕ) → m < n → A
[]       ! zero  [ ()      ]
[]       ! suc _ [ ()      ]
(a ∷ as) ! zero  [ _       ] = a
(a ∷ as) ! suc m [ s≤s m≤n ] = as ! m [ m≤n ]
\end{code}

Define `_!'_` with the help of `_!_[_]` in one line!

\begin{code}
_!''_ : ∀ {n}{A : Set} → Vec A n → Fin' n → A
| as !'' (n , p) = as ! n [ p ]
\end{code}

| TODO: point-free ugyanez uncurry segítségével

Exercise: define conversion functions between `Fin` and `Fin'`!
