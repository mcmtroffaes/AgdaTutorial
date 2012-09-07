% Boolean Values
% Péter Diviánszky
% 2011. 05. 03.

\begin{code}
module Bool_a where
\end{code}



The `Bool` Set
==============

Definition of `Bool` with two elements `true` and `false`:

\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}

*Interpretation:*

 * `Bool`  ∈ `Set`
 * `true`  ∈ `Bool`
 * `false` ∈ `Bool`
 * and there is nothing else in `Bool`

It is because of the last point that the syntax of the definition doesn't look like this:

~~~~~~~~~~~~~~~~~
Bool  ∈ Set
true  ∈ Bool
false ∈ Bool
~~~~~~~~~~~~~~~~~

--------------------

-   `data` and `where` are keywords
-   `Set` is the set of sets (a constant)
-   `:` is pronounced "is a" or "elem of", it has the same rule as '∈' in set theory.
-   Indentation matters!
-   Spaces are needed!
-   We call `true` and `false` _constructors_ of _data type_ `Bool` (and at the same time `true` and `false` are elements of set `Bool`)


`not`, `_∧_`: Boolean Functions
===============================

Negation:

\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}

This is a function that has `Bool` as domain and `Bool` as range. We can pattern match on the elements that appear in set `Bool` namely `true` and `false` to define how the function works.

Logical AND:

\begin{code}
_∧_   : Bool → Bool → Bool
true  ∧ x = x
false ∧ x = false

infixr 6 _∧_
\end{code}

---------------

-   Underscores in names like `_∧_` denote the space for the operands.
-   `infixr` ...
-   Logical AND could be defined with four alternatives.


Exercise: `_∨_`
=========


A) Define logical OR:

\begin{code}
infixr 5 _∨_

_∨_   : Bool → Bool → Bool
true  ∨ _ = true --
false ∨ x = x --
\end{code}

B) Define logical OR with one alternative, with the help of `not` and `_∧_`!

\begin{code}
infixr 5 _∨₁_ --

_∨₁_   : Bool → Bool → Bool --
x ∨₁ y = not (not x ∧ not y) --
\end{code}

Exercise
=========

Define a set named `Answer` with three elements, `yes`, `no` and `maybe`.

Define logical operations on `Answer`!


Exercise
=========

Define a set named `Quarter` with four elements, `east`, `west`, `north` and `south`.

Define a function `turnLeft : Quarter → Quarter`.

Define the functions `turnBack` and `turnRight` with the help of `turnLeft`! (By either pattern matching or defining specific function composition function.)

If you have multiple elements of the same set you can define these in one line:
\begin{code}
data name : Set where
  elem1 elem2 elem3 : name
\end{code}

