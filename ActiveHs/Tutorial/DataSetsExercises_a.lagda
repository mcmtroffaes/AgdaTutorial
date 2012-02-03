% Additional Exercises (Data Sets)
% Ambrus Kaposi
% 2011. 09. 15.

\begin{code}
module DataSetsExercises_a where
\end{code}


Exercise
========

Define the `MaybeBool` (has 3 elements) and `Maybe` datasets.

Define an isomorphic definition of `Maybe A` with the help of `_⊎_` and `⊤` and conversion functions.


Non-regular recursive set
=========================

List the first smallest 4 (+4) elements of the following dataset (let A = ⊤ and B = Bool and reversed):

\begin{code}
data AlterList (A B : Set) : Set  where
  []  :                     AlterList A B
  _∷_ : A → AlterList B A → AlterList A B
\end{code}


Mutually Recursive Sets
=======================

`List₁` and `List₂` are mutually recursive sets:

\begin{code}
mutual
  data List₁ (A B : Set) : Set  where
    []  :                 List₁ A B
    _∷_ : A → List₂ A B → List₁ A B

  data List₂ (A B : Set) : Set  where
    _∷_ : B → List₁ A B → List₂ A B
\end{code}

List the smallest first 5 elements of `List₁ ⊤ Bool`!
