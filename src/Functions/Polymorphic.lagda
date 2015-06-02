% Polymorphic Functions
% Ambrus Kaposi and Péter Diviánszky
% 2011. 09. 15.

Import list
===========

\begin{code}
module Functions.Polymorphic where

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

Remember this is a polymorphic definition.


`_++_` : Concatenation on lists
===============================

Using the definition of the `List` set above, the definition of list
concatenation can be given as follows:

\begin{code}
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_
\end{code}

The `_++_` operator works with `List`s parametrised by arbitrary `Set`s.
We call its parameters polymorphic, and thus `_++_` a polymorphic function.
Polymorphic parameters have to be named explicitly in beginning of the
declaration of the function by putting them into curly braces:

    f : {A B C : Set} → ...

****************

In Agda, polymorphic parameters are explicit, in Haskell they are implicit.

Instead of curly braces we can use also round braces but then
we have to give the set as a parameter at every function call, which
may make it clearer but also more inconvenient to use.

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
---------

1. Define two functions that define an isomorphism between `List ⊤` and `ℕ`.
   That is, the following functions should be implemented:

     `fromList : List ⊤ → ℕ`  
     `toList   : ℕ → List ⊤`

1. Show on a sheet of paper with equational reasoning that the `fromList`
   function is a bijection and it preserves the `_+_` and `_++_`
   operations (that is, `∀ a, b ∈ List ⊤ . fromList (a ++ b) = fromList a + fromList b` always holds).

1. Define a `Maybe` set (a list with 0 or 1 elements) together with the
   `head` and `tail` functions for the polymorphic `List` type, with the
   help of `Maybe`.

1. Define the following functions on lists:

     `map  : {A B : Set} → (A → B)      → List A → List B -- regular map`  
     `maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map`

1. Define the singleton list function:

     `[_] : {A : Set} → A → List A`

<!--
\begin{code}
fromList : List ⊤ → ℕ
fromList []        = zero --
fromList (tt ∷ xs) = suc (fromList xs) --

toList   : ℕ → List ⊤
toList zero    = [] --
toList (suc n) = tt ∷ toList n --

map  : {A B : Set} → (A → B)      → List A → List B -- regular map
map f []       = [] --
map f (x ∷ xs) = f x ∷ map f xs --

maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map
maps []       _        = [] --
maps _        []       = [] --
maps (f ∷ fs) (x ∷ xs) = f x ∷ (maps fs xs) --

[_] : {A : Set} → A → List A
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

Polymorphic identity function: `id`
===================================

<!--
| If we tend to put an `_` in place of a parameter it probably means that it can be made implicit, that is, we could rely on Agda to guess the value. We can do this putting the parameter in curly braces:
-->

Similarly to the concatenation function above, a polymorphic identity
function can be also given with the same notation, which is an example
of generic polymorphic functions.

\begin{code}
id : {A : Set} → A → A
id a = a
\end{code}

If we want we can specify the implicit (hidden) parameter manually in
curly braces:

\begin{code}
aNumber = id {ℕ} (suc zero)
\end{code}

Exercises
---------

1. Define the `const : {A B : Set} → A → B → A` function.

1. Define the `flip : {A B C : Set} → (A → B → C) → B → A → C` function.


`_×_`: Cartesian product
========================

Recall the definition of the product set:

\begin{code}
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_
\end{code}

Exercises
---------

1. Define a function that swaps the two elements.

1. Define the following functions:

     `proj₁ : {A B : Set} → A × B → A`  
     `proj₂ : {A B : Set} → A × B → B`

<!--
\begin{code}
proj₁ : {A B : Set} → A × B → A
proj₁ (a , _) = a --

proj₂ : {A B : Set} → A × B → B
proj₂ (_ , b) = b --
\end{code}
-->

`_⊎_`: Disjoint union (sum)
===========================

Recall the definition of the sum set:

\begin{code}
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_
\end{code}

Exercises
---------

1. Define a function that swaps the two elements.

1. Define the eliminator function for disjoint union:

     `[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)`

<!--
\begin{code}
[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[_,_] f g (inj₁ a) = f a --
[_,_] f g (inj₂ b) = g b --
\end{code}
-->
