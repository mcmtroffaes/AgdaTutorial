% Boolean Values
% Péter Diviánszky
% 2011. 05. 03.


First Agda module
==============

Our first Agda module contains no definition just a *module header*:

\begin{code}
module Bool_a where
\end{code}

 * `module` and `where` are keywords
 * The module name after `module` should correspond to the file name.  
   In this case the file name is `Bool.agda`.
 * Syntax highlighting is added by loading the module with C-`c` C-`l`.

The following definitions are added one-by-one to the file.


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

It is because of the last two point that the syntax of the definition doesn't look like this:

~~~~~~~~~~~~~~~~~ {.haskell}
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



Question
===============

Suppose we have another Boolean set defined:

\begin{code}
data Bool' : Set where
  true'  : Bool'
  false' : Bool'
\end{code}

Are `Bool` and `Bool'` the same set?  
If not, which one is the "real" Booleans?


Isomorphic sets
===============

`Bool` and `Bool'` are *definitionally* different but they are *isomorphic*.*

Two sets are isomorphic if there is an isomorphism between them i.e.
a one-to-one relation between the elements.**

------------

*Taking the constructor names into account they are even *canonically isomorphic*
i.e. there is a canonical isomorphism between them.

**We define the formal notion of isomorphism later in Agda.


Representations and interpretations
===============


TODO: figure



Both `Bool` and `Bool'` may represent the Booleans; it is the choice
of the programmer which one to use (or group of programmers in collaboration).





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



