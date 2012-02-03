% Element of
% Ambrus Kaposi
% 2011. 10. 20.

\begin{code}
module Elem_a where
\end{code}


Import List
===========

\begin{code}
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)
\end{code}


`_∈_` proposition
===============

\begin{code}
data _∈_ {A : Set}(x : A) : List A → Set where
  first : {xs : List A} → x ∈ x ∷ xs
  later : {y : A}{xs : List A} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_
\end{code}

| lehetne a konstruktorokat head-nek meg tail-nek is nevezni

Exercises
=========

Define the following functions:

\begin{code}
singleton : ∀ {A}{x : A} → x ∈ x ∷ []
| singleton = first
nonempty  : ∀ {A}{x : A}{xs : List A} → x ∈ xs → xs ≡ [] → ⊥
| nonempty first     ()
| nonempty (later p) ()

_!_ : ∀{A : Set} → List A → ℕ → Maybe A -- getting the nth element of the list
| []     ! _       = nothing
| x ∷ xs ! zero    = just x
| x ∷ xs ! (suc n) = xs ! n

infix 5 _!_

!→∈   : ∀ {A}(n : ℕ)(x : A)(xs : List A) → xs ! n ≡ just x →  x ∈ xs
| !→∈ zero    x []        ()
| !→∈ zero    x (.x ∷ xs) refl = first
| !→∈ (suc n) x []        ()
| !→∈ (suc n) x (x' ∷ xs) p    = later (!→∈ n x xs p)
index : ∀ {A}{x : A}(xs : List A) → x ∈ xs → ℕ
| index []       ()
| index (x ∷ xs) first     = 0
| index (x ∷ xs) (later p) = index xs p
\end{code}
