% The Dependent Pair

\begin{code}
module Sets.Sigma where
\end{code}


Import list
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


Usage
=====

A dependent pair may represent:

-   a disjoint union of a family of (data) types,
-   a subset of a set,
-   existential quantification.


`Σ` as disjoint union
=====================

Some examples of where `Σ` could be used as disjoint union:

-   `List A` ~ `Σ ℕ (Vec A)`
-   `Σ ℕ Fin` is the type that contains all `Fin`s.

Note that the non-dependent pair and the disjoint union of two types are
special cases of `Σ`:

-   `A × B` ~ `Σ A (const B)`
-   `A ⊎ B` ~ `Σ Bool (λ b → if b then A else B)`


`Σ` as subset
=============

If `A` is a type and `P` is a predicate on `A` then we could
represent the set of elements that fulfill the predicate by `Σ A P`.

Examples:

-   `Vec A n`      ~ `Σ (List A) (λ l → length l ≡ n)`
-   `Fin n`        ~ `Σ ℕ (λ m → m < n)`
-   balanced trees ~ `Σ` tree `(λ t → t` is balanced`)`


Exercise
--------

Define the `toFin` function for the `Fin′` type.

\begin{code}
Fin′ : ℕ → Set
Fin′ n = Σ ℕ (λ x → x < n)

toFin : ∀ {n} → Fin′ n → Fin n
\end{code}

<!--
\begin{code}
toFin (zero  , s≤s m≤n) = zero
toFin (suc n , s≤s m≤n) = suc (toFin (n , m≤n))
\end{code}
-->


`Σ` as existential quantification
=================================

Let `A` be a type and let `P` be a predicate on `A`.  There exists
(constructively) an element of `A` for which `P` holds iff
the subset `Σ A P` is non-empty.

Examples:

-   `a ≤ b` ~ `Σ ℕ (λ k → k + a ≡ b)`
-   `even n` ~ `Σ ℕ (λ k → n ≡ 2 * k)`
-   `odd n` ~ `Σ ℕ (λ k → n ≡ 1 + 2 * k)`
-   `a ∈ as` ~ `Σ ℕ (λ k → as ! k ≡ a)`

Note that there we could interpret the `Σ A (λ x → P(x))` pattern as
`∃ x ∈ A . P(x)`.


Other use of `Σ`
================

`Σ` can also be very handy when a function needs to return a value
together with a proof of that the given value has some property.

For example:

\begin{code}
data _∈_ {A : Set}(x : A) : List A → Set where
  first : {xs : List A} → x ∈ x ∷ xs
  next  : {y : A}{xs : List A} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

_!_ : ∀{A : Set} → List A → ℕ → Maybe A
[]       ! _       = nothing
(x ∷ xs) ! zero    = just x
(x ∷ xs) ! (suc n) = xs ! n

infix 5 _!_
\end{code}

Exercise
--------

In connection to this example, define the `lookup` function:

\begin{code}
lookup : ∀ {A}{x : A}(xs : List A) → x ∈ xs → Σ ℕ (λ n → xs ! n ≡ just x)
\end{code}

*Hint:* Use the `with` keyword.

<!--
\begin{code}
lookup []       ()
lookup (x ∷ xs) first     = 0 , refl
lookup (x ∷ xs) (next p) with lookup xs p
lookup (_ ∷ _)  (next p) | n , q = suc n , q
\end{code}
-->

Exercise
--------

Consider the following definitions that declare the isomorphism (known from
earlier) between `List ⊤` and `ℕ`.

\begin{code}
fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

lemma : ∀ {a b : ℕ} → Data.Nat.suc a ≡ Data.Nat.suc b → a ≡ b
lemma refl = refl

from-injection : ∀ {a b} → (fromList a) ≡ (fromList b) → a ≡ b
from-injection {[]}      {[]}      refl = refl
from-injection {[]}      {x ∷ xs}  ()
from-injection {x ∷ xs}  {[]}      ()
from-injection {tt ∷ xs} {tt ∷ ys} p = cong (_∷_ tt) (from-injection {xs} {ys} (lemma p))
\end{code}

Now, define the following function:

\begin{code}
from-surjection : ∀ (n : ℕ) → Σ (List ⊤) (λ t → (fromList t) ≡ n)
\end{code}

*Hint:* Use the `with` keyword.

<!--
\begin{code}
from-surjection zero = [] , refl
from-surjection (suc n) with from-surjection n
from-surjection (suc n) | l , p = tt ∷ l , cong suc p
\end{code}
-->
