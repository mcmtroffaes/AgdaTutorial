% Import Declarations

\begin{code}
module Modules.Imports where
\end{code}


Detach a module in a separate file
==================================

Module definitions can be detached into separate files:

1.  A file named *modulename*`.agda` should contain the module declaration.
1.  Now the module declaration can be replaced by an import declaration.


Example
=======

\begin{code}
module X where

  module ImportExample where

    data Bool : Set where
      false true : Bool

  x = ImportExample.true
\end{code}

can be replaced by

\begin{code}
module X′ where

  import ImportExample  -- click to see the contents of ImportExample.agda

  x = ImportExample.true
\end{code}


Search paths
============

Agda source files should be acessible from the Agda search paths.

In the Emacs environment, the Agda search paths can be set by

1.  M-`x` `customize-group` <return> `agda2` <return>
    (M stands for Meta which is labelled Alt on most computers)
2.  Edit the contents of `Agda2 Include dirs`

The default search paths are the current directory
(from where `emacs` was started) and the path of the Standard
Libraries if it was installed properly.

If you invoke the Agda compiler from the command line,
you can add a path to the search paths by the `-i` flag.
The default search path is the current directory.


Qualified modules in import declarations
=======

Module definitions can be detached into separate files
contained in (possibly nested) directories acessible from the search paths.

Example:

\begin{code}
module X″ where

  module ImportExample where

    data Bool : Set where
      false true : Bool

  x = ImportExample.true
\end{code}

can be replaced by

\begin{code}
module X‴ where

  import Modules.ImportExample  -- click to see the contents of Modules/ImportExample.agda

  x = Modules.ImportExample.true
\end{code}

Note that the top level module declaration of `Modules/ImportExample.agda` 
declares the qualified module `Modules.ImportExample`.
Qualified module declaration are allowed only in this case.


Renaming imported modules
==============

One can rename imported modules:

\begin{code}
module X⁗ where

  import Modules.ImportExample as ImportExample

  x = ImportExample.true
\end{code}


Syntactic abbreviations
==============

`open import` M

stands for

`import` M  
`open` M

There are similar abbreviations for `using`, `hiding`, `renaming`, `public` constructs.

