% Enumerated Sets

<!--
\begin{code}
module Sets.Enumerated where
\end{code}
-->


The `Bool` set
==============

Definition of `Bool` with two elements `true` and `false`:

\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}

*Interpretation:*

 * `Bool`  is a `Set`
 * `true`  is a `Bool`
 * `false` is a `Bool`
 * there is nothing else which is `Bool`
 * `true` and `false` are different

It is because of the last two points that the syntax of the definition doesn't look like this:

~~~~~~~~~~~~~~~~~ 
Bool  : Set
true  : Bool
false : Bool
~~~~~~~~~~~~~~~~~


--------------------

-   `data` and `where` are keywords
-   `Set` is the set of sets (a constant)
-   ':' is pronounced "is a" or "type of", it has similar rule as '∈' in set theory.  
    We do not use the '∈' symbol because ':' and '∈' have different behaviour which will be highlighted later.
-   Indentation matters!
-   Spaces are needed!
-   We call `true` and `false` _constructors_ of _data type_ `Bool` (more explanations of constructors come later)


 
Exercises
=========

A) Define a set named `Answer` with three elements, `yes`, `no` and `maybe`.

B) Define a set named `Quarter` with four elements, `east`, `west`, `north` and `south`.



Questions
===============

Suppose we have `Bool'` defined:

\begin{code}
data Bool' : Set where
  true'  : Bool'
  false' : Bool'
\end{code}

1.  Are `Bool` and `Bool'` the same set?  
1.  If not, which one is the "real" set of Booleans?


Isomorphic sets
===============

`Bool` and `Bool'` are *definitionally* different but they are *isomorphic*.

Two sets are isomorphic if there is an isomorphism between them i.e.
a one-to-one relation between the elements.

We will define the formal notion of isomorphism in Agda
and we will be able to convert values between isomorphic sets.



Representation and interpretation
===============

Both `Bool` and `Bool'` may represent the Booleans; it is the choice
of the programmer or group of programmers which one to use.

Interpretation (or meaning) is the opposite relation to representation.

-   The interpretation (the meaning) of `Bool` is the set of Boolean values.
-   One possible representation of the set of Booleans is `Bool`.
-   Another possible representation of the set of Booleans is `Bool'`.
-   `Bool` and `Bool'` are isomorphic - different representations of the same concept should be isomorphic.

Different interpretations of the same definition is also possible as we will see.


Special finite sets
===========

We can define finite sets with n = 0, 1, 2, ... elements.

Two special cases with n = 0 and n = 1:

\begin{code}
data ⊥ : Set where   -- There is no constructor.

data ⊤ : Set where
  tt : ⊤
\end{code}

We will use `⊥` as the empty set and `⊤` as the one-element set.  
(These have special roles as you will see.)


---------------

`tt` stands for trivially true.

If we define two empty sets they will be different, unlike in set theory.  
(Type theory differs from set theory; we prefer type theory for several reasons.)


Syntactic abbreviation
======================

If you have multiple elements of the same set you can define these in one line:
\begin{code}
data name : Set where
  elem1 elem2 elem3 : name
\end{code}



