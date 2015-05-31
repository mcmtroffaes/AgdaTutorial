% Emacs Usage
% Péter Diviánszky, Ambrus Kaposi and Gábor Páli
% 2012.

<!--
\begin{code}
module Emacs_Usage where
\end{code}
-->

Emacs commands
==============

An Emacs window is called a frame and inside a frame we can open multiple buffers, each file opens in a new buffer. Frames can be managed from the `File` menu while buffers from the `Buffers` menu. Each buffer has an associated mode which is shown on the info line at the bottom of the buffer in parentheses.

`C` stands for Ctrl, `M` for Meta (or Alt)

----------------- -----------------------------------------
M-`x`             execute any Emacs command after typing command name \<return\> (tab completion available)
C-`x` C-`f`       find file (open, new)
C-`x` C-`s`       save
C-`x` C-`c`       exit Emacs
C-`x` `1`         maximize buffer
C-`_`             undo
C-`g`             cancel
C-`w`             cut
C-`y`             yank (paste)
C-`u` C-`x` `=`   name of symbol under cursor (available also from the Agda drop-down menu)
----------------- -----------------------------------------

--------------

Some other useful commands:

----------------- -----------------------------------------
C-`k`             kill line (cut whole line)
M-`d`             cut word
C-`s`             forward search
C-`r`             backward search
C-`s` C-`w` C-`s` search for word under cursor
C-`x` Left        switch to previous buffer
C-`x` Right       switch to next buffer
C-`x` C-`w`       save as
----------------- -----------------------------------------



Emacs Agda-mode commands
========================

This section is only for reference.

----------------- -----------------------------------------
C-`c` C-`l`       load (type checking)
C-`c` C-`f`       forward (jump to next hole)
C-`c` C-`b`       backward (jump to previous hole)
C-`c` C-`d`       deduce (type of expression)
C-`c` C-`n`       normalize (evaluate expression)
M-`.`             jump to definition
M-`*`             jump back
----------------- -----------------------------------------

Note that you can also find the same (and further more) commands in the
`Agda` submenu on the menu bar.


Commands inside a hole
----------------------

----------------- -----------------------------------------
C-`c` C-`,`       information about the hole
C-`c` C-`d`       deduce (type of contents of hole)
C-`c` C-Space     give (checks whether the term in the hole has the right type and if it has, replaces the hole with the term)
C-`c` C-`c`       case split (pattern match on variables)
C-`c` C-`r`       refine (one step further)
C-`c` C-`a`       auto (try to find a solution)
----------------- -----------------------------------------

See also the context-sensitive menu on the right click inside a hole.


Emacs Agda-mode Unicode symbols
===========================

----------------------- -------------------
`\->`                   `→`
`\bn`, `\bz`, `\bq`     `ℕ`, `ℤ`, `ℚ`
`\Gl`                   `λ`
`\top`, `\bot`          `⊤`, `⊥`
`\o`                    `∘`
`\_0`, `\_1`, `\_2`     `₀`, `₁`, `₂`
`\u+`                   `⊎`
`\x`                    `×`
`\or`, `\and`           `∨`, `∧`
`\lub`, `\glb`          `⊔`, `⊓`
`\::`                   `∷`
`\<=`, `\==`            `≤`, `≡`
`\lfloor`, `\rfloor`    `⌊`, `⌋`
----------------------- -------------------

<!--
| Typing exercises
| ----------------
-->





