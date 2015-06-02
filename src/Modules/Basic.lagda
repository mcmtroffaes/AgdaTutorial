% Modules
% Péter Diviánszky
% 2013. 01.


Module headers
==============

Every Agda module should have a *module header* like as follows:

\begin{code}
module Modules.Basic where
\end{code}

Note that:

 * The `module` and the `where` are keywords.
 * The module name after `module` should correspond to the file name in the
   file system.  In this case the file name is `Modules/Basic.agda` (or
   `Modules/Basic.lagda`).
 * Syntax highlighting is added by successfully loading the module in Emacs with
   C-`c` C-`l`.


Exercise
--------

1.  Install the Agda compiler.
1.  Open a file called `First.agda` (or something similar) in Emacs.
1.  Fill in the module header.
1.  Load the module to get syntax highlighting.


Declarations
==============

An Agda module is a module header and a list of declarations.

In the following slides we will see declarations like

-   set definitions
-   function definitions
-   import declarations
-   ...
