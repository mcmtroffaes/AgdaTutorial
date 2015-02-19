Usage
-----

An online HTML version can be found at

http://people.inf.elte.hu/divip/AgdaTutorial/Index.html


Local Builds
------------

1.  Set up a sandbox.

        cabal sandbox init

2.  Clone Agda and PandocAgda (note: divipp's Agda fork is required
    until https://github.com/agda/agda/pull/29 is merged).

        git clone git@github.com:divipp/agda.git ../agda
        git clone git@github.com:agda/agda-stdlib.git ../agda-stdlib
        git clone git@github.com:divipp/PandocAgda.git ../PandocAgda

3.  Install the git versions of agda and PandocAgda.

        cabal install ../agda ../PandocAgda

4.  Generate the html view of the tutorial.

        cabal exec agdapandoc -- -i ../agda-stdlib/src -i tutorial/src --html tutorial/src/Index.lagda --css=Agda.css


Development
-----------

This Agda tutorial is under development.

Any contribution is welcome!
