Usage
-----

An online HTML version can be found at

http://people.inf.elte.hu/pgj/agda/tutorial/


Local Builds
------------

1.  Set up a sandbox.

        cabal sandbox init

2.  Clone Agda and PandocAgda.

        git clone git@github.com:agda/agda.git ../agda
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
