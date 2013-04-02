% Functions Defined by Cases

\begin{code}
module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)
\end{code}


Negation as a function
============================

Representation of negation as a function from `Bool` to `Bool`:

\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}

We pattern match on the elements that appear in set `Bool` namely `true` and `false` to define how the function works.


Computational content of functions
==================================

We have elements of `Bool` like

`not true : Bool`  
`not (not (not false)) : Bool`  

but these are not new elements: their normal form is either `true` or `false`.

In the interactive environment we can compute the normal form by C-`c` C-`n`.

Functions have *computational content*.  
For example, `not` defines not just a relation between `Bool` and `Bool`,
but also an algorithm how to compute the negated value.


Logical AND
===============================

Logical AND could be defined with four alternatives but
here is a shorter definition with two alternatives with variables:
 
\begin{code}
_∧_   : Bool → Bool → Bool
true  ∧ x = x
false ∧ _ = false

infixr 6 _∧_
\end{code}


-   We can use variables as patterns.
-   We can use wildcard (an underscore) as a pattern.  
    A wildcard pattern is an unnamed variable.
-   Similar to data sets
    -   Underscores in names like `_∧_` denote the space for the operands.
    -   `infixr` gives the fixity


Exercise: `_∨_`
=========


A) Define logical OR:

\begin{code}
infixr 5 _∨_
 
_∨_   : Bool → Bool → Bool
\end{code}

<!--
\begin{code}
true  ∨ _ = true --
false ∨ x = x --
\end{code}
-->
 
B) Define logical OR with one alternative, with the help of `not` and `_∧_`!

<!--
\begin{code}
infixr 5 _∨₁_ --

_∨₁_   : Bool → Bool → Bool --
x ∨₁ y = not (not x ∧ not y) --
\end{code}
-->
 
Exercises
=========

A)  Define a set named `Answer` with three elements, `yes`, `no` and `maybe`.

    Define logical operations on `Answer`!
 
B)  Define a set named `Quarter` with four elements, `east`, `west`, `north` and `south`.

    Define a function `turnLeft : Quarter → Quarter`.
 
    Define the functions `turnBack` and `turnRight` with the help of `turnLeft`! (By either pattern matching or defining a specific function composition function.)




