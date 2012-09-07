% Disjoint Union
% Ambrus Kaposi
% 2011. 09. 15.

\begin{code}
module Union_a where
\end{code}


`_⊎_`: Disjoint Union (Sum)
===================================

Definition:

\begin{code}
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_
\end{code}

Exercises:

 * What are the elements of `Bool ⊎ ⊤`?
 * What are the elements of ⊤ ⊎ (⊤ ⊎ ⊤)?
 * Name an already learned isomorphic type to `⊤ ⊎ ⊤`!


Neutral element of `_⊎_`
========================

Exercise: how should we define `Bottom` so that ∀ A : Set. `Bottom ⊎ A` would be isomorphic to `A`?

***************

\begin{code}
data ⊥ : Set where
\end{code}

There is no constructor.

Exercise:
=========

Define the eliminator function for disjoint union:

\begin{code}
[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[_,_] f g (inj₁ a) = f a --
[_,_] f g (inj₂ b) = g b --
\end{code}
