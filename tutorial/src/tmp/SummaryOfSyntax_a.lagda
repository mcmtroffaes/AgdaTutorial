% Summary of Syntax

\begin{code}
module SummaryOfSyntax_a where
\end{code}


Here is all the new syntax (and some semantical info) we learn grouped by chapters.

Data Sets
=========

Bool

 * You should always begin your filename.agda file with the following line:
   \begin{code}
   module filename where\end{code}
 * `data`, `where`, `:` (∈), `Set`
 * indentation, need of spaces, arbitrary variable names
 * `_` (placeholder for parameters), `infix`*
 * totality (need to specify all cases while pattern matching)
 * `→`

ℕ

 * \begin{code}
   {-# BUILTIN NATURAL ℕ    #-}
   {-# BUILTIN ZERO    zero #-}
   {-# BUILTIN SUC     suc  #-}\end{code}
 * holes: `?`, `{! !}`
 * totality (all functions need to terminate)

List

 * parameterised datatypes
 * `_` (unnamed parameter)
 * polymorphic functions: `{A B : Set} →` ...
 * implicit parameters

Product

Union


Predicates
==========

≤

 * dependent types
 * indexed types vs. parametrised types
 * `open`, `import`, `using`
 * `∀` notation
 * .-ed patterns

Equality

 * equational reasoning


| valahol: 
| `_` (Agda should guess (there is only 1 solution))
| data Answer : Set where
|   yes no maybe : Answer
| nincs class system
| (A B : Set) --> (A : Set) (B : Set)
| inductive family definition valahol általánosan
| mixfix operators
| comments: --, {- -}

| should contain links to the corresponding chapter
