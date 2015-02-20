% Infix Notation

\begin{code}
module Syntax.Infix where

open import Data.Bool using (Bool; true; false)
\end{code}


Infix notation
==============

\begin{code}
data BinTree' : Set where
  x : BinTree'
  _+_ : BinTree' → BinTree' → BinTree'
\end{code}

yields

~~~~~~~~~~~~~~~~~ 
BinTree' : Set
x : BinTree'
x + x : BinTree'
(x + x) + x : BinTree'
x + (x + x) : BinTree'
(x + x) + (x + x) : BinTree'
...
~~~~~~~~~~~~~~~~~

Underscores in names like `_+_` denote the space for the operands.  

One can give the precedence with `infix`, `infixl` or `infixr`:

\begin{code}
infixr 3 _+_
\end{code}

yields

~~~~~~~~~~~~~~~~~ 
BinTree' : Set
x : BinTree'
x + x : BinTree'
(x + x) + x : BinTree'
x + x + x : BinTree'
(x + x) + x + x : BinTree'
...
~~~~~~~~~~~~~~~~~

(so `_+_` has right precedence)


