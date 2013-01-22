% Polymorphic Functions
% Ambrus Kaposi and Péter Diviánszky
% 2011. 09. 15.

Import list
===========

\begin{code}
module Polymorphism_a where

open import Data.Nat
open import Data.Unit using (⊤; tt)
\end{code}


Definition of `List`
==============

Recall the definition of `List`:

\begin{code}
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
\end{code}


`_++_` : Concatenation on Lists
===========================

Definition of concatenation:

\begin{code}
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_
\end{code}

`_++_` works with `List`s parametrised by arbitrary `Set`s. 
We call this parameter a polymorphic parameter and `_++_` a polymorphic function.
Polymorphic parameters have to be named explicitly in beginning of the declaration of the function by putting them into curly braces:

    f : {A B C : Set} → ...

****************

In Agda, polymorphic parameters are explicit, in Haskell they are implicit.

Instead of curly braces we can use also round braces but then
we should give the set as a parameter at every function call.



<!--
| Exercises: `head` and `tail` on Lists
| ====================================
| 
| Try to define the following functions:
| 
| \begin{code}
| head₀ : {A : Set} → List A → A
| head₀ []       = {!!} --
| head₀ (x ∷ xs) = x --
| \end{code}
| 
| \begin{code}
| tail₀ : {A : Set} → List A → List A
| tail₀ []       = [] --
| tail₀ (x ∷ xs) = xs --
| \end{code}
| 
| Define the following functions:
| 
| \begin{code}
| head₁ : List ℕ → ℕ
| head₁ []       = 0 --
| head₁ (x ∷ xs) = x --
| \end{code}
| 
| \begin{code}
| tail₁ : List ℕ → List ℕ
| tail₁ []       = [] --
| tail₁ (x ∷ xs) = xs --
| \end{code}
| 
| Define the following functions (`head` should return `[]` for empty lists and a singleton list for non-empty lists):
| 
| \begin{code}
| head₂ : {A : Set} → List A → List A
| head₂ []       = [] --
| head₂ (x ∷ xs) = x ∷ [] --
| \end{code}
| 
| \begin{code}
| tail₂ : {A : Set} → List A → List (List A)
| tail₂ []       = [] --
| tail₂ (x ∷ xs) = xs ∷ [] --
| \end{code}
-->

Exercises
=========

*   Define two functions which define the isomorphism between `List ⊤` and `ℕ`!

\begin{code}
fromList : List ⊤ → ℕ
\end{code}

<!--
\begin{code}
fromList []        = zero --
fromList (tt ∷ xs) = suc (fromList xs) --
\end{code}
-->

\begin{code}
toList   : ℕ → List ⊤
\end{code}

<!--
\begin{code}
toList zero    = [] --
toList (suc n) = tt ∷ toList n --
\end{code}
-->

*   Show on a sheet of paper with equational reasoning that the `fromList` function is a bijection and it preserves the `_+_` and `_++_` operations (that is, `∀ a, b ∈ List ⊤ . fromList (a ++ b) = fromList a + fromList b`).

*   Define a `Maybe` set (lists with 0 or 1 elements)
    and `head` and `tail` functions for the polymorphic `List` type with the help of `Maybe`.



Exercises
=========

Define the following functions on lists:

\begin{code}
map  : {A B : Set} → (A → B)      → List A → List B -- regular map
\end{code}

<!--
\begin{code}
map f []       = [] --
map f (x ∷ xs) = f x ∷ map f xs --
\end{code}
-->

\begin{code}
maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map
\end{code}

<!--
\begin{code}
maps []       _        = [] --
maps _        []       = [] --
maps (f ∷ fs) (x ∷ xs) = f x ∷ (maps fs xs) --
\end{code}
-->

Define the singleton list function:

\begin{code}
[_] : {A : Set} → A → List A
\end{code}

<!--
\begin{code}
[ a ] = a ∷ [] --
\end{code}
-->

<!--
| Polymorphic `id` function
| =========================
| 
| Let's define an id function on Natural numbers:
| 
| \begin{code}
| idℕ : ℕ → ℕ
| idℕ n = n
| \end{code}
| 
| This is the way we can make it polymorphic:
| 
| \begin{code}
| id₀ : (A : Set) → A → A
| id₀ _ a = a
| \end{code}
| 
| We gave a name (`A`) to the first parameter which has to be in `Set`. We can refer to named parameters in the sets which define later parameters.
| 
| Usage:
| 
| \begin{code}
| aNumber₀ = id₀ ℕ (suc zero)
| aNumber₁ = id₀ _ (suc zero)
| \end{code}
| 
| In the second case we let Agda guess the value of the first parameter.
-->

Polymorphic `id` function
=========================

<!--
| If we tend to put an `_` in place of a parameter it probably means that it can be made implicit, that is, we could rely on Agda to guess the value. We can do this putting the parameter in curly braces:
-->

\begin{code}
id : {A : Set} → A → A
id a = a
\end{code}

If we want, can specify the implicit paramter manually in curly braces:

\begin{code}
aNumber = id {ℕ} (suc zero)
\end{code}

Exercise
========

Define `const : {A B : Set} → A → B → A`!

Define `flip : {A B C : Set} → (A → B → C) → B → A → C`!



`_×_`: Cartesian Product
========================

Recall the definition of Cartesian product:

\begin{code}
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_
\end{code}

Exercises
=========

Define a function which swaps the two element!

Define the following functions:

\begin{code}
proj₁ : {A B : Set} → A × B → A
\end{code}

<!--
\begin{code}
proj₁ (a , _) = a --
proj₂ : {A B : Set} → A × B → B
proj₂ (_ , b) = b --
\end{code}
-->

`_⊎_`: Disjoint Union (Sum)
===================================

Recall the definition

\begin{code}
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_
\end{code}


Exercises
=========

Define a function which swaps the two element!

Define the eliminator function for disjoint union:

\begin{code}
[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
\end{code}

<!--
\begin{code}
[_,_] f g (inj₁ a) = f a --
[_,_] f g (inj₂ b) = g b --
\end{code}
-->

