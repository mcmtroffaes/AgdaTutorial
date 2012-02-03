% Sets
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module DataSets_a where
\end{code}



Syntax
==================

We describe sets with *generators*, which tells how to
construct elements of the set.

General syntax:

`data` *name* *parameters* `: Set  where`  
\ \ \ \ *generator₁*  
\ \ \ \ *generator₂*  
\ \ \ \ ...

Generators are in form *name* `:` *set*.  
Generator names are called *constructors*.



`Bool`, `⊤`, `⊥`: Sets Given by Enumeration
=================

Definition of set `Bool` with two elements `true` and `false`:

\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}

Definition of set `⊤` with one element `tt`:

\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}

Definition of set `⊥` with no elements:

\begin{code}
data ⊥ : Set where
\end{code}


Constructors with Parameters
============================

`MaybeBool` has three elements but just two constructors!

\begin{code}
data MaybeBool : Set where
  nothing :        MaybeBool
  just    : Bool → MaybeBool
\end{code}

`just` is not an element of `MaybeBool`, it is an element of `Bool → MaybeBool`, the function space
from `Bool` to `MaybeBool`.

Elements of `MaybeBool`:

`MaybeBool` = { `nothing`; `just true`; `just false` }


`Maybe`: The Safe Null-Pointer
============================

`MaybeBool` can be generalized to `Maybe` which has one parameter:

\begin{code}
data Maybe (A : Set) : Set where
  nothing :     Maybe A
  just    : A → Maybe A
\end{code}

`MaybeBool` ~ `Maybe Bool`.

*Exercise:*  

What are the elements of `Maybe ⊤` and `Maybe ⊥`?


Infix Operators
===============


`_⊎_`: Disjunct Union
============================

Disjunct union has two parameters:

\begin{code}
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
\end{code}

Notes

-   Underscore in `_⊎_` denotes infix notation.
-   `(A B : Set)` is a shorthand form of `(A : Set) (B : Set)`

*Example:*

`Bool ⊎ ⊤` = { `inj₁ true`; `inj₁ false`; `inj₂ tt` }

`Bool` ~ `⊤ ⊎ ⊤`

`Maybe A` ~ `⊤ ⊎ A`


Set Element Definitions
=======================


`_×_`: Cartesian Product
===================================

The definition of Cartesian product:

\begin{code}
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
\end{code}

*Example:*  
Elements of `Bool × Bool` (the extra space is needed before the comma):

     true , true 
     true , false
     false , true
     false , false


`ℕ`: Natural Numbers
==============

Definition of natural numbers is *recursive*, i.e. at least
one constructor refers to the set defined:

\begin{code}
data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ
\end{code}

Elements of `ℕ`:

    zero
    suc zero
    suc (suc zero)
    ...

Note that we may use `0`, `1`, `2`, ... instead of `zero`, `suc zero`, ...*

************************

*\ Decimal natural number literals can be used if we bind our `ℕ` set to the Agda internals with the following three declarations:

\begin{code}
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
\end{code}


`List`: Lists
=============================

List is a recursive set with a parameter:

\begin{code}
data List (A : Set) : Set where
  []  :              List A
  _∷_ : A → List A → List A

infixr 5 _∷_
\end{code}

`ℕ` ~ `List ⊤`

*Example:*  
Elements of `List Bool`:

    []  
    true  ∷ []  
    false ∷ []  
    true  ∷ true  ∷ []  
    false ∷ true  ∷ []  
    true  ∷ false ∷ []  
    false ∷ false ∷ []  
    ...


|    -> szabadon generáltak, minden különbözőképpen előállított elem különböző

