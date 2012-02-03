% Lists
% Ambrus Kaposi
% 2011. 09. 15.

\begin{code}
module List_a where
\end{code}


Definition of `List`
==============

Definition of `List`:

\begin{code}
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
\end{code}

*Interpretation*: `List A` ∈ `Set`, where `A` ∈ `Set`. We call `A` a parameter of `List` and we can refer to `A` in the definition of the set elements.

*Example:* elements of `List Bool`:

    []  
    true  ∷ []  
    false ∷ []
    true  ∷ true  ∷ []  
    false ∷ true  ∷ []  
    true  ∷ false ∷ []  
    false ∷ false ∷ []  
    ...


`_++_` : Concatenation on Lists
===========================

Definition of concatenation:

\begin{code}
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_
\end{code}

We want `_++_` to work with `List`s parametrised by arbitrary `Set`s. We call this parameter a polymorphic parameter and `_++_` a polymorphic function.
Polymorphic parameters have to be named explicitly in beginning of the declaration of the function by putting them into curly braces:

\begin{code}
f : {A B C : Set} → ...
\end{code}



Exercises: `head` and `tail` on Lists
====================================

Try to define the following functions:

\begin{code}
head : {A : Set} → List A → A
tail : {A : Set} → List A → List A
\end{code}

Define the following functions:

\begin{code}
head : List ℕ → ℕ
tail : List ℕ → List ℕ
\end{code}

Define the following functions (`head` should return `[]` for empty lists and a singleton list for non-empty lists):

\begin{code}
head : {A : Set} → List A → List A
tail : {A : Set} → List A → List (List A)
\end{code}

Define a `Maybe` set and `head` and `tail` functions for the polymorphic `List` type with the help of `Maybe`.


Exercises
=========

Define the following functions on lists:

\begin{code}
map  : {A B : Set} → (A → B)      → List A → List B -- regular map
maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map
\end{code}

Define the singleton list function:

\begin{code}
[_] : {A : Set} → A → List A
\end{code}


Polymorphic `id` function
=========================

Let's define an id function on Natural numbers:

\begin{code}
idℕ : ℕ → ℕ
idℕ n = n
\end{code}

This is the way we can make it polymorphic:

\begin{code}
id₀ : (A : Set) → A → A
id₀ _ a = a
\end{code}

We gave a name (`A`) to the first parameter which has to be in `Set`. We can refer to named parameters in the sets which define later parameters.

Usage:

\begin{code}
aNumber₀ = id ℕ (suc zero)
aNumber₁ = id _ (suc zero)
\end{code}

In the second case we let Agda guess the value of the first parameter.

**************

In Agda, polymorphic parameters are explicit, in Haskell they are implicit.

Polymorphic `id` function with implicit parameter
=================================================

If we tend to put an `_` in place of a parameter it probably means that it can be made implicit, that is, we could rely on Agda to guess the value. We can do this putting the parameter in curly braces:

\begin{code}
id : {A : Set} → A → A
id a = a
\end{code}

If we want, we can still specify it manually in curly braces:

\begin{code}
aNumber = id {ℕ} (suc zero)
\end{code}

Exercise
========

Define the polymorphic const function!
