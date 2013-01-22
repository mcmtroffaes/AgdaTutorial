% Vectors
% Ambrus Kaposi
% 2011. 11. 17.

\begin{code}
module Vec_a where
\end{code}

Imports
=======

\begin{code}
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _<_; s≤s)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
\end{code}


Definition
===========

`Vec A n` is the type of n-length vectors containing elements of type A:

\begin{code}
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_
\end{code}

Similarity with the type of natural numbers that contains the size of the number (that is, itself):

\begin{code}
data ℕ* : ℕ → Set where
  zero : ℕ* zero
  suc  : ∀ {n} → ℕ* n → ℕ* (suc n)
\end{code}

*Exercise:* give an `A` for which `Vec A` is isomorphic to `ℕ*`!

Concatenation has the same structure as `_+_` for natural numbers:

\begin{code}
_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ as ++ bs
\end{code}

*Question:* how does Agda know that the indices of the types should be simply added?

| C-nel (no check) biztonsagosabb, Java-nal (runtime check) gyorsabb


Exercises
==========

Define head and tail functions for `Vec`s! Hint: they should only work for vectors of length > 1.

\begin{code}
head : ∀ {n}{A : Set} → Vec A (suc n) → A
head (a ∷ as) = a --
tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
tail (a ∷ as) = as --
\end{code}

The simple map is safer than the map for `List`s because we know that that the size of the vector remains the same after mapping a function over it:

\begin{code}
map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (a ∷ as) = f a ∷ map f as
\end{code}

Define elementwise map:

\begin{code}
maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = [] --
maps (f ∷ fs) (a ∷ as) = f a ∷ maps fs as --
\end{code}

Define the safe lookup function:

\begin{code}
_!_[_] : ∀ {n}{A : Set} → Vec A n → (m : ℕ) → m < n → A
[]       ! zero  [ ()      ] --
[]       ! suc _ [ ()      ] --
(a ∷ as) ! zero  [ _       ] = a --
(a ∷ as) ! suc m [ s≤s m≤n ] = as ! m [ m≤n ] --
\end{code}

Define the following functions:

\begin{code}
replicate : ∀ {n}{A : Set} → A → Vec A n
replicate {zero}  a = [] --
replicate {suc n} a = a ∷ replicate a --

zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n
zip []       []       = [] --
zip (a ∷ as) (b ∷ bs) = (a , b) ∷ zip as bs --

foldl₀ : ∀ {n}{A B : Set} → (B → A → B) → B → Vec A n → B
foldl₀ _⊕_ b []       = b --
foldl₀ _⊕_ b (a ∷ as) = foldl₀ _⊕_ (b ⊕ a) as --

foldl : ∀ {A : Set} (B : ℕ → Set) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero → Vec A m → B m
foldl B _⊕_ b []       = b --
foldl B _⊕_ b (a ∷ as) = foldl (λ n → B (suc n)) _⊕_ (b ⊕ a) as --

foldr₀ : ∀ {n}{A B : Set} → (A → B → B)→ B → Vec A n → B
foldr₀ _⊕_ b []       = b --
foldr₀ _⊕_ b (a ∷ as) = a ⊕ foldr₀ _⊕_ b as --
\end{code}
