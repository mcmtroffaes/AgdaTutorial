% Enumerated Sets

<!--
\begin{code}
module Sets.Enumerated where
\end{code}
-->


The `Bool` set
==============

Consider the definition of `Bool` with two elements, `true` and `false`:

\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}

*Interpretation:*

 * `Bool`  is a `Set`.
 * `true`  is a `Bool`.
 * `false` is a `Bool`.
 * There is *nothing else* that is `Bool`.
 * `true` and `false` are different values.

It is due to last two points that the syntax of the definition does not look
like that:

~~~~~~~~~~~~~~~~~
Bool  : Set
true  : Bool
false : Bool
~~~~~~~~~~~~~~~~~


--------------------

Note that:

-   The `data` and the `where` are keywords.

-   The `Set` is the set of sets (a constant).

-   The ':' is pronounced "is a" or "type of", it has similar rule as '∈'
    in set theory.  We do not use the '∈' symbol because ':' and '∈' have
    different meanings which will be discussed in details later.

-   Indentation matters.

-   Spaces matter.

-   We call `true` and `false` _constructors_ of the _data type_ `Bool`
    (more explanation on constructors will come later).



Exercises
---------

1. Define a set named `Answer` with only three elements: `yes`, `no`, and
   `maybe`.

1. Define a set named `Direction` with only four elements: `east`, `west`,
   `north`, and `south`.


Questions
===============

Consider the following definition of `Bool'`:

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
-   Different interpretations of the same definition are also possible as we will see.


Special finite sets
===========

We can define finite sets with $n = 0, 1, 2, \ldots$ elements.

The special case with $n = 0$ is the empty set:

\begin{code}
data ⊥ : Set where   -- Note that there is no constructor at all.
\end{code}

The special case with $n = 1$ is the singleton set (a set with one element):

\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}

`⊥` and `⊤` have interesting interpretations as we will see.


Types vs. sets
===========

Basic differences between types and sets:

-   The type of an element is unique ↔ an element can be member of different
    sets.  E.g. `true` cannot be the element of two different types at the
    same time.

-   A type is not just the collection of its elements ↔ a set is characterized
    by its elements.  E.g. there are different empty types.

Thus `data` defines *types*, not sets.

-   We prefer types over sets for several reasons.

-   From now on, we use both terms "type" and "set" for types.
    We use the term "element" for types too.

-   `Set` is the type of types, so it should be called `Type`.  However,
    Agda 2.3.2 and before (and probably after too) calls it `Set`.

-   Agda makes it possible to give the same name to the constructors of
    different types -- but only if each constructor application remains
    unambiguous that way.


Syntactic abbreviation
======================

If we have multiple elements of the same type, it is possible to define them
in one line:

\begin{code}
data name : Set where
  elem₁ elem₂ : name
\end{code}



