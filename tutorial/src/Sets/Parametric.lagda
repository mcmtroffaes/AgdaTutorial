% Parametric Sets
% Ambrus Kaposi and Péter Diviánszky
% 2011. 09. 15.



Import List
===========

\begin{code}
module Sets.Parametric where
open import Data.Nat
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





Exercises
=========

* What is the connection between `List ⊤` and `ℕ`?
* Define a `Maybe` set (lists with 0 or 1 elements)!
* Define parametric trees (various sorts)!



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


Exercises
=========

 * How many elements are there in `⊤ × ⊤`, `⊤ × ⊥`, `⊥ × ⊤` and `⊥ × ⊥`?
 * How should we define `Top` so that ∀ A : Set. `Top × A` would be isomorphic to `A` (neutral element of `_×_`)?


`_⊎_`: Disjoint Union (Sum)
===================================

Definition:

\begin{code}
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_
\end{code}


Exercises
=========

 * What are the elements of `Bool ⊎ ⊤`?
 * What are the elements of `⊤ ⊎ (⊤ ⊎ ⊤)`?
 * Name an already learned isomorphic type to `⊤ ⊎ ⊤`!
 * How should we define `Bottom` so that ∀ A : Set. `Bottom ⊎ A` would be isomorphic to `A` (Neutral element of `_⊎_`)?
 * Give an isomorphic definition of `Maybe A` with the help of `_⊎_` and `⊤`!


Mutually recursive sets
=======================

`List₁` and `List₂` are mutually recursive parametric sets:

\begin{code}
data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  []  :                 List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ (A B : Set) where
  _∷_ : B → List₁ A B → List₂ A B
\end{code}

*Exercise:* list the smallest first 7 elements of `List₁ ⊤ Bool`!


Non-regular recursive set
=========================

Consider the following data set:

\begin{code}
data AlterList (A B : Set) : Set  where
  []  :                     AlterList A B
  _∷_ : A → AlterList B A → AlterList A B
\end{code}

List the 4 smallest elements of `AlterList ⊤ Bool`, and
the 5 smallest elements of `AlterList Bool ⊤`.

Nested set
==========

`Square`, the set of square matrices with 2^n^ rows, is nested, because at least
one of its constructors refers to the set defined with more complex
parameter(s):


\begin{code}
data T4 (A : Set) : Set where
  quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
  zero :            A  → Square A   -- 2^0 rows
  suc  : Square (T4 A) → Square A   -- 2^(n+1) rows
\end{code}


*Example:*

Set                     1st,                           2nd,                                 3rd,     ...
----------------------- ------------------------------ ------------------------------------ -------- ---
`Square ℕ` = {          `zero 3`; `zero 16`; ...;      `suc (zero (t4 1 2 3 4))`; ...;      `x`;...; ...
`Square (T4 ℕ)`= {      `zero (t4 1 2 3 4)`; ...;      `suc (zero (t4 (t4 ...) ...))`; ...; ...;     ...
`Square (T4 (T4 ℕ))`= { `zero (t4 (t4 ...) ...)`; ...; ...;                                 ...;     ...
...                     ...                            ...                                  ...      ...

`x : Square ℕ`  
`x = suc (suc (zero (t4 (t4 1 2 3 4) (t4 5 6 7 8) (t4 9 10 11 12) (t4 13 14 15 16))))`

~~~~~~~ {.latex}
\left(\begin{array}{cccc}1&2&5&6\\3&4&7&8\\9&10&13&14\\11&12&15&16\end{array}\right)
~~~~~~~

***************

Nested sets are special non-regular sets.  
Nested sets can be translated to mutually recursive regular sets.





