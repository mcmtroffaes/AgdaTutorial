% Cartesian Product
% Ambrus Kaposi
% 2011. 09. 15.

\begin{code}
module Product_a where
\end{code}


`_×_`: Cartesian Product
========================

The definition of Cartesian product:

\begin{code}
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_
\end{code}

`(A B : Set)` is the way of specifying a set that is parameterised by two sets.

*Example:*  
Elements of `Bool × Bool` (the extra space is needed before the comma):

     true , true 
     true , false
     false , true
     false , false


Neutral element of `_×_`
========================

Exercise: how should we define `Top` so that ∀ A : Set. `Top × A` would be isomorphic to `A`?

***************

\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}

`tt` stands for trivially true


Exercises
=========

What are the elements of `⊤ × ⊤`?

Define the following functions:

\begin{code}
proj₁ : {A B : Set} → A × B → A
proj₂ : {A B : Set} → A × B → B
\end{code}


Exercise: isomorphism between `ℕ` and `List ⊤`
===============================

Define the following functions:

\begin{code}
fromList : List ⊤ → ℕ
toList   : ℕ → List ⊤
\end{code}

Show on a sheet of paper that the `fromList` function is a bijection and it preserves the `_+_` and `_++_` operations (that is, `∀ a, b ∈ List ⊤ . fromList (a ++ b) = fromList a + fromList b`).
