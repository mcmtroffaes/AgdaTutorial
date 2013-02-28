% Sigma
% Ambrus Kaposi
% 2011. 11. 17.

\begin{code}
module Sigma_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
\end{code}


Dependent pair
==============

The generalization of `_×_` is called `Σ` (Sigma) or dependent pair:

\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ A B

infixr 4 _,_
\end{code}

We can define the two main type constructions can with the help of `Σ`:

 * `A × B` ~ `Σ A (const B)`
 * `A ⊎ B` ~ `Σ Bool (λ b → if b then A else B)`

We can create a subset of type `A` by giving a predicate `P` on `A`:

 * `Vec A n`      ~ `Σ (List A) (λ l → length l ≡ n)`
 * `Fin n`        ~ `Σ ℕ        (λ m → m < n)`
 * balanced trees ~ `Σ` tree   `(λ t → t` is balanced`)`

`Σ` concatenates a family of types:

 * `List A` ~ `Σ ℕ (Vec A)`
 * `Σ ℕ Fin` is the type that containts all `Fin`s.

Existential quantification can be expressed with `Σ`:

 * `a ≤ b` ~ `Σ ℕ (λ k → k + a ≡ b)`
 * `even n` ~ `Σ ℕ (λ k → n ≡ 2 * k)`
 * `odd n` ~ `Σ ℕ (λ k → n ≡ 1 + 2 * k)`
 * `a ∈ as` ~ `Σ ℕ (λ k → as ! k ≡ a)`


Examples
========

Define `toFin`:

\begin{code}
Fin' : ℕ → Set
Fin' n = Σ ℕ (λ x → x < n)

toFin : ∀ {n} → Fin' n → Fin n
toFin (zero  , s≤s m≤n) = zero --
toFin (suc n , s≤s m≤n) = suc (toFin (n , m≤n)) --
\end{code}

Sigma is very handy when a function needs to return a value and a proof that the value has some property. Example:

\begin{code}
data _∈_ {A : Set}(x : A) : List A → Set where
  first : {xs : List A} → x ∈ x ∷ xs
  later : {y : A}{xs : List A} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

_!_ : ∀{A : Set} → List A → ℕ → Maybe A
[] ! _           = nothing
x ∷ xs ! zero    = just x
x ∷ xs ! (suc n) = xs ! n

infix 5 _!_

lookup : ∀ {A}{x : A}(xs : List A) → x ∈ xs → Σ ℕ (λ n → xs ! n ≡ just x)
lookup []       ()
lookup (x ∷ xs) first     = 0 , refl
lookup (x ∷ xs) (later p) with lookup xs p
lookup (_ ∷ _)  (later p) | n , q = suc n , q 
\end{code}


How to express bijection
========================

We haven't finished the [proof](Equality_a.html#list-ℕ) of the isomorphism of `ℕ` and `List ⊤` because we were not able to define surjection without `Σ`.

\begin{code}
fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

lemm : ∀ {a b : ℕ} → Data.Nat.suc a ≡ Data.Nat.suc b → a ≡ b
lemm refl = refl

from-injection : ∀ {a b} → fromList a ≡ fromList b → a ≡ b
from-injection {[]}      {[]}      refl = refl
from-injection {[]}      {x ∷ xs}  ()
from-injection {x ∷ xs}  {[]}      ()
from-injection {tt ∷ xs} {tt ∷ ys} p = cong (_∷_ tt) $ from-injection {xs} {ys} (lemm p)
\end{code}

*Exercise:* define the following function:

\begin{code}
from-surjection : ∀ (n : ℕ) → Σ (List ⊤) (_≡_ n ∘ fromList)
from-surjection zero = [] , refl --
from-surjection (suc n) with from-surjection n --
from-surjection (suc n) | l , p = tt ∷ l , cong suc p --
\end{code}
