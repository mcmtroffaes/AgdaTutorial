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

1.  Are `Bool` and `Bool'` the same sets?  
1.  If not, which one is the "real" set of Booleans?


Isomorphisms
==========

`Bool` and `Bool'` are definitionally different but they are *isomorphic*.

*   Two sets are isomorphic if there is a one-to-one relation between their elements.
*   We will represent isomorphisms in Agda later.


Representation and interpretation
===============

Interpretation (or meaning) is the opposite relation to representation.

-   The interpretation (the meaning) of `Bool` is the set of Boolean values.
-   One possible representation of the set of Booleans is `Bool`.
-   Another possible representation of the set of Booleans is `Bool'`.
-   Different interpretations of the same definition is also possible as we will see.


Special finite sets
===========

We can define finite sets with n = 0, 1, 2, ... elements.

The special case with n = 0 is the empty set:

\begin{code}
data ⊥ : Set where   -- There is no constructor.
\end{code}

The special case with n = 1 is the singleton set (set with one element):

\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}

`⊥` and `⊤` have interesting interpretations as we will see.


Types vs. sets
===========

Basic differences between types and sets:

-   The type of an element is unique ↔ an element can be member of different sets  
    E.g. `true` cannot be the element of two different type at the same time.
-   A type is not the collection of its elements ↔ a set is characterized by its elements  
    E.g. there are different empty types.

`data` defines types, no sets!  

-   We prefer types over sets for several reasons.
-   From now on, we use both terms 'type' and 'set' for types.  
    We use the term 'element' for types too.
-   `Set` is the type of types, so it should be called `Type`.  
    Agda 2.3.2 and before (and probably after too) calls it `Set`.
-   Agda allows to give the same name to constructors of different types,  
    if at each constructor application the type is unambiguous.


Syntactic abbreviation
======================

If we have multiple elements of the same type we can define these in one line:

\begin{code}
data name : Set where
  elem₁ elem₂ : name
\end{code}

x

