% Installation
% Péter Diviánszky, Ambrus Kaposi and Gábor Páli
% 2012.

<!--
\begin{code}
module Installation where
\end{code}
-->

Agda compiler
============

General installation instruction can be found at the [Download](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download) section of the Agda website.

The following instructions may be out of date.


Linux or FreeBSD
---------

If you have Ubuntu / Debian / NixOS / some other decent Linux distro or FreeBSD, you can safely install Agda from your package manager. Or you can use cabal-install as described below for the Windows version.

After installation show Emacs where to find agda-mode by the following command:

`agda-mode setup`

Windows
-----------

1. If you don't have Haskell platform and you have administrator access to the computer, try the [all-in-one Windows installer](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Windows).
1. If you already have Haskell platform installed (and maybe don't have adminsitrator access), you need to go through the following steps:

    1. Put GHC into `%PATH%` (cmd: `set PATH=%PATH%;"C:\Program Files\Haskell Platform\2011.2.0.1\bin";`)
    1. install [Emacs](http://www.gnu.org/software/emacs/)
    1. put Emacs into `%PATH%` (cmd: `set PATH=%PATH%;"c:\program files (x86)\emacs-23.3\bin";`)
    1. put the cabal/bin folder into `%PATH%` (cmd: `set PATH=%PATH%;%APPDATA%\cabal\bin;`)
    1. cmd: `cabal update`
    1. cmd: `cabal install agda`
    1. `agda-mode setup`  
       If that fails, you have two opportunities:
        1. put `(load-file (let ((coding-system-for-read ‘utf-8)) (shell-command-to-string “agda-mode locate”)))` into your `.emacs` file (path is usually `Users/username/AppData/Roaming/.emacs`)
        1. after starting emacs, type `(load-file (let ((coding-system-for-read ‘utf-8)) (shell-command-to-string “agda-mode locate”)))` into the *scratch* buffer, select it with the mouse and type `M-x eval-region`

1. If you neither have administrator access nor Haskell Platform installed: get administrator access!


Standard library
==================

You can download the Agda standard libraries from [here](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary).

This is how to teach Agda see the standard libraries using the following commands in Emacs.
Note that it requires [haskell-mode](http://projects.haskell.org/haskellmode-emacs/)
to be installed first.

1.  `M-x load-library` \<return\> `agda2-mode` \<return\>  
1.  `M-x customize-group` \<return\> `agda2` \<return\>  
   (`M` stands for Meta which is labelled Alt on most computers)
1.  Search for: `Agda2 Include dirs`
1.  Type here the path of the Agda libraries something like  
   `/home/divip/share/lib-0.6/src`
1.  On top of the buffer click on this button:
   `Save for future sessions`

-------------

When we use the standard library modules for the first time it takes some time to load them because Agda is compiling them.




