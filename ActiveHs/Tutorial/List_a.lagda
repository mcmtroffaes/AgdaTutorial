% Lists
% Ambrus Kaposi
% 2011. 09. 15.



Import List
===========

\begin{code}
module List_a where
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






| `_++_` : Concatenation on Lists
| ===========================
| 
| Definition of concatenation:
| 
| \begin{code}
| _++_ : {A : Set} → List A → List A → List A
| []       ++ ys = ys
| (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
| 
| infixr 5 _++_
| \end{code}
| 
| We want `_++_` to work with `List`s parametrised by arbitrary `Set`s. We call this parameter a polymorphic  parameter and `_++_` a polymorphic function.
| Polymorphic parameters have to be named explicitly in beginning of the declaration of the function by putting them into curly braces:
| 
|     f : {A B C : Set} → ...
| 
| 
| 
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
| 

Exercises
=========

* What is the connection between `List ⊤` and `ℕ`?
* Define a `Maybe` set (lists with 0 or 1 elements)!
| and `head` and `tail` functions for the polymorphic `List` type with the help of `Maybe`.
* Define paramteric trees (various sorts)!



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

`List₁` and `List₂` are mutually recursive sets:

\begin{code}
mutual
  data List₁ (A B : Set) : Set  where
    []  :                 List₁ A B
    _∷_ : A → List₂ A B → List₁ A B

  data List₂ (A B : Set) : Set  where
    _∷_ : B → List₁ A B → List₂ A B
\end{code}

*Exercise:* list the smallest first 5 elements of `List₁ ⊤ Bool`!


Non-regular recursive set
=========================

List the first smallest 4 (+4) elements of the following dataset (let `A` = `⊤` and `B` = `Bool` and reversed):

\begin{code}
data AlterList (A B : Set) : Set  where
  []  :                     AlterList A B
  _∷_ : A → AlterList B A → AlterList A B
\end{code}


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

Nested are special non-regular sets.  
Nested sets can be translated to mutually recursive regular sets.





| 
| Exercises
| =========
| 
| Define the following functions on lists:
| 
| \begin{code}
| map  : {A B : Set} → (A → B)      → List A → List B -- regular map
| map f []       = [] --
| map f (x ∷ xs) = f x ∷ map f xs --
| 
| maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map
| maps []       _        = [] --
| maps _        []       = [] --
| maps (f ∷ fs) (x ∷ xs) = f x ∷ (maps fs xs) --
| \end{code}
| 
| Define the singleton list function:
| 
| \begin{code}
| [_] : {A : Set} → A → List A
| [ a ] = a ∷ [] --
| \end{code}
| 
| 
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
| 
| **************
| 
| In Agda, polymorphic parameters are explicit, in Haskell they are implicit.
| 
| Polymorphic `id` function with implicit parameter
| =================================================
| 
| If we tend to put an `_` in place of a parameter it probably means that it can be made implicit, that is, we could rely on Agda to guess the value. We can do this putting the parameter in curly braces:
| 
| \begin{code}
| id : {A : Set} → A → A
| id a = a
| \end{code}
| 
| If we want, we can still specify it manually in curly braces:
| 
| \begin{code}
| aNumber = id {ℕ} (suc zero)
| \end{code}
| 
| Exercise
| ========
| 
| Define the polymorphic const function!


