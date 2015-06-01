% Functions Defined by Cases

\begin{code}
module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)
\end{code}


Negation as a function
======================

Representation of negation as a function from `Bool` to `Bool`:

\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}

We pattern match on the elements that appear in the `Bool` set
&mdash; that is `true` and `false` &mdash; in order to define how the
function works.


Computational content of functions
==================================

Now we have got elements of `Bool` like as follows:

`not true : Bool`  
`not (not (not false)) : Bool`  

Note that these are not new elements: their normal form is still either `true`
or `false`.  In the interactive environment, we can compute those normal forms
by the C-`c` C-`n` key combination.

The reason is that functions have a certain *computational content*.  For
example, `not` defines not only a relation between `Bool` and `Bool`, but it
also presents an algorithm on how to compute the negated value.


Logical conjunction
===================

The logical conjunction could be defined with pattern matching on all the
possible four alternatives (that is, as a table), but here is a shorter
definition with only two alternatives and with variables:

\begin{code}
_∧_   : Bool → Bool → Bool
true  ∧ x = x
false ∧ _ = false

infixr 6 _∧_
\end{code}

Note the following:

-   We can use variables as patterns.

-   We can use wildcards (underscores) as patterns.  A wildcard pattern can
    also be considered as an unnamed variable.

-   Similarly to data sets:

    -   Underscores in names &mdash; such as `_∧_` &mdash; denote the space for
        the operands.

    -   The `infixr` keyword gives the associativity and precedence.


Exercises
---------

1. Define the logical disjunction as a function.

     `infixr 5 _∨_`  
     `_∨_   : Bool → Bool → Bool`

1. Redefine the logical disjunction in a single line, with the help of `not`
   and `_∧_` functions.

1. Define a set named `Answer` with three elements: `yes`, `no`, and `maybe`.
   Define the logical conjunction and disjunction operations on `Answer`.

1. Define a set named `Quarter` with four elements: `east`, `west`, `north`,
   and `south`.  Define the `turnLeft` function with the following type:

     `turnLeft : Quarter → Quarter`

1. For the previous exercise, define the `turnBack` and `turnRight` functions
   with the help of `turnLeft`.

     `turnRight : Quarter → Quarter`  
     `turnBack  : Quarter → Quarter`

     (This can be done with either pattern matching or defining the function
     composition (`_∘_`) and using it.)


\begin{code}
infixr 5 _∨_

_∨_   : Bool → Bool → Bool
true  ∨ _ = true --
false ∨ x = x --
\end{code}

<!--
\begin{code}
infixr 5 _∨₁_ --

_∨₁_   : Bool → Bool → Bool --
x ∨₁ y = not (not x ∧ not y) --
\end{code}
-->
