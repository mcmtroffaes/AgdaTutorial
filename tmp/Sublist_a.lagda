% Sublist
% Ambrus Kaposi
% 2011. 10. 20.

\begin{code}
module Sublist_a where
\end{code}


Import List
===========

\begin{code}
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
\end{code}


Sublist Predicate
=================

\begin{code}
data _⊆_ {A : Set} : List A → List A → Set where
    stop :                                              [] ⊆ []
    drop : {xs ys : List A} → {y : A} → xs ⊆ ys →       xs ⊆ (y ∷ ys)
    keep : {xs ys : List A} → {x : A} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

infix 4 _⊆_
\end{code}

You can type `⊆` as `\sub=`.

*Exercise*: define these functions:

\begin{code}
e0 : 1 ∷ [] ⊆ 1 ∷ []
e0 = keep stop --
e1 : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
e1 =  keep $ keep $ drop stop --
\end{code}




`with` construct
==============

We'd like to define a filter function for lists:

\begin{code}
filter₀ : {A : Set} → (A → Bool) → List A → List A
filter₀ p []               = []
filter₀ p (x ∷ xs) = if (p x) then x ∷ filter₀ p xs else filter₀ p xs

-- filter₁ : {A : Set} → (A → Bool) → List A → List A
-- filter₁ p []               = []
-- filter₁ p (x ∷ xs) | p x = x ∷ filter₁ p xs -- Haskell boolean guards
--                    | _   = filter₁ p xs

filter₂ : {A : Set} → (A → Bool) → List A → List A
filter₂ p []       = []
filter₂ p (x ∷ xs) with p x
filter₂ p (x ∷ xs) | true  = x ∷ filter₂ p xs
filter₂ p (x ∷ xs) | false = filter₂ p xs

filter : {A : Set} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs -- only syntactic sugar
... | false = filter p xs
\end{code}



Exercise
========

Prove that the result of filtering a list will be sublist of the original list:

\begin{code}
lem-filter : {A : Set} → (p : A -> Bool) → (xs : List A) → filter p xs ⊆ xs
lem-filter p [] = stop --
lem-filter p (x ∷ xs) with p x --
... | true  = keep (lem-filter p xs) --
... | false = drop (lem-filter p xs) --
\end{code}



`⊆` is a partial order
======================

*Exercise*: prove that `⊆` is reflexive and transitive:

\begin{code}
⊆-refl  : ∀ {A}(xs : List A) → xs ⊆ xs
⊆-refl []       = stop --
⊆-refl (x ∷ xs) = keep (⊆-refl xs) --
⊆-trans : {A : Set}{xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans stop     q        = q --
⊆-trans p        (drop q) = drop $ ⊆-trans p q --
⊆-trans (drop p) (keep q) = drop $ ⊆-trans p q --
⊆-trans (keep p) (keep q) = keep $ ⊆-trans p q --
\end{code}

*Exercise*: show that this simple property holds:

\begin{code}
⊆-drop : ∀ {A}{x : A}{xs ys} → x ∷ xs ⊆ ys → xs ⊆ ys
⊆-drop (drop p) = drop $ ⊆-drop p --
⊆-drop (keep q) = drop q --
\end{code}

What about the other direction?

\begin{code}
⊆-antidrop : ∀ {A}{x : A}{xs} → x ∷ xs ⊆ xs → ⊥
⊆-antidrop (drop p) = ⊆-antidrop $ ⊆-drop p
⊆-antidrop (keep p) = ⊆-antidrop p
\end{code}

Another definition where the base case of the recursion is explicit:

\begin{code}
⊆-antidrop' : ∀ {A}(x : A)(xs : List A) → x ∷ xs ⊆ xs → ⊥
⊆-antidrop' x   []        ()
⊆-antidrop' x   (x' ∷ xs) (drop p) = ⊆-antidrop' x' xs (⊆-drop p) 
⊆-antidrop' .x' (x' ∷ xs) (keep p) = ⊆-antidrop' x' xs p
\end{code}

Now we can prove that `⊆` is antisymmetric:

\begin{code}
⊆-antisymm : ∀ {A}(xs ys : List A) → xs ⊆ ys → ys ⊆ xs → xs ≡ ys
⊆-antisymm []       []       stop stop = refl
⊆-antisymm []       (y ∷ ys) _    ()
⊆-antisymm (x ∷ xs) []       ()   _
⊆-antisymm (x ∷ xs) (y ∷ ys)  (drop p) (drop q) with ⊆-antidrop $ ⊆-trans (drop p) q
...                                                | ()
⊆-antisymm (x ∷ xs) (.x ∷ ys) (drop p) (keep q) with ⊆-antidrop $ ⊆-trans p q
...                                                | ()
⊆-antisymm (x ∷ xs) (.x ∷ ys) (keep p) (drop q) with ⊆-antidrop $ ⊆-trans q p
...                                                | ()
⊆-antisymm (x ∷ xs) (.x ∷ ys) (keep p) (keep q) = cong (_∷_ x) $ ⊆-antisymm xs ys p q
\end{code}

Now we know that `⊆` is a partial order over lists.
