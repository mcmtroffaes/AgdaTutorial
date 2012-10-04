% A Practical Agda Tutorial
% Péter Diviánszky
% 2012. 09. 19.

\begin{code}
module About_a where
\end{code}


*for AIM XVI*

Goal
====

Let people play and explore some programming in Agda without theoretical background.


Ideology
========

Assumptions

-   Most IT people are not interested in theory in the first place.
-   One can go on a long way without any theoretical knowledge in Agda.  
    *   The proposed tutorial is a demonstration for this.
-   Much background theoretical remarks interrupts the playing experience.
-   Students react quite differently to theoretical remarks.  
    (confused ↔ want to know a lot more)
-   People who already played with Agda are more
    open to theoretical background.  
    *   We give pointers on a separate page.  
        There are pointers on that page into the tutorial.


Goal details
============

**Subgoals**
:   -   Give the semantics of Agda programs by examples.
    -   Teach Agda programming skills.
        *   when to use which language construct
    -   Give a methodology to write correct Agda programs.
        *   what does program correctness mean
        *   how to be more sure that the program is correct
**Requirements**
:   * Only secondary school mathematics is required.
    * no Haskell, type theory, category theory, ...
    * followable without a tutor
**Audience**
:   - for newcomers


Resources
=========

This is the 4th semester we teach Agda at ELTE Budapest.

-   13 week × 90 min
-   3-8 students
-   Lecturers: Péter Diviánszky and Ambrus Kaposi*  
-   The course material is revised each semester.

*********

*We also learn as we teach which may be inspired this practical tutorial.



Planned methodology
===========

Tutorial: *Idiomatic solutions for practical exercises taken into pieces, sorted and explained.*


1.  Collect interesting exercises for students
    -   practical problems like **roman numerals, leap years, ...**
1.  Write idiomatic Agda solutions for the problems.
    A)   **specification** (mainly with data types)
    B)   implementation (functions)
1.  Take the solutions into incremental pieces.
    -   essential problems like sorting should appear here!
1.  Sort the pieces by the language constructs/techniques used.
    -   **data types first, functions later**
    -   ...
1.  Fill in semantic gaps with ad-hoc exercises.
    -   revisit non-idiomatic code when the idiomatic solution is possible
    -   try to **avoid this step**
1.  Hide all Agda code!  
    Unhide code for the first appearence of any language construct/technique used and add **very practical explanations**.

---------------

The emphasised parts are the features of this tutorial,
especially what kind of problems we take in the 1st step.

We can improve at every step 1-6 which explains that the tutorial is rewritten every time.


Social contract
===============


-   remain freely available and ready to fork
    -   *Problem:* we have to give univ. students different exercises...
-   give citation of sources if applicable
-   try to merge with similar tutorials if any


State of art
============

-   Only ~1/6 is ready.
-   The methodology is not strictly followed yet.
    -   There are too much ad-hoc exercises.
-   Currently Peter is working on it as the autumn semester goes on.


Demo
========

[We visit the current tutorial.](Index_a.xml)



Thank you for listening!
========


Thank you for any feedback.  


