% Infix Notation

\begin{code}
module Syntax.Infix where

open import Sets.Enumerated using (Bool; true; false)
\end{code}


Infix notation
==============

Consider this definition:

\begin{code}
data BinTree' : Set where
  x : BinTree'
  _+_ : BinTree' → BinTree' → BinTree'
\end{code}

There one can note that it basically yields the following:

~~~~~~~~~~~~~~~~~
BinTree' : Set
x : BinTree'
x + x : BinTree'
(x + x) + x : BinTree'
x + (x + x) : BinTree'
(x + x) + (x + x) : BinTree'
...
~~~~~~~~~~~~~~~~~

Underscores in names &mdash; like `_+_` above &mdash; are placeholders for
operands.

One can also give the precedence with `infix`, (non-associative),
`infixl` (left-associative) or `infixr` (right-associative).

For example the single line below:

\begin{code}
infixr 3 _+_
\end{code}

yields the following:

~~~~~~~~~~~~~~~~~
BinTree' : Set
x : BinTree'
x + x : BinTree'
(x + x) + x : BinTree'
x + x + x : BinTree'
(x + x) + x + x : BinTree'
...
~~~~~~~~~~~~~~~~~

(So, now `_+_` has the right precedence, and it became right-associative.)
