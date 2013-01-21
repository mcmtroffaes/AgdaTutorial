% Introduction to Agda


Introduction
------------

\begin{code}
module Index_a where

import Motivation_a
import Technical_Info_a
\end{code}

Sets
----

\begin{code}
import Bool_a       -- Enumeration
import Nat_a        -- Recursion
import List_a       -- Parameter
import Indices_a    -- Indices
import Inference_a  -- Term inference
import LessThan_a   -- Propositions
import Equality_a   -- Parameters vs. indices
\end{code}


Functions
---------

\begin{code}
import Patterns_a
import Recursion_a
import Polymorphism_a
import Large_a          -- Set result
import Proofs_a
import EqProof_a        -- Equality proofs
\end{code}

Other
-----

[Presentation for mathematicians](http://people.inf.elte.hu/divip/Agda.pdf)

\begin{code}
import About_a
\end{code}


Lecture notes under revisition
------------------------------

\begin{code}
import Vec_a
import Fin_a
import Sigma_a
import Parity_a
import Ordering_a
import Dec_a
import Logic_Agda_a
\end{code}

[Logic_Haskell_a.lhs](Logic_Haskell_a.lhs)


| TODO
| ----
|
| Example_a.lagda
| 
| talk about agda termination check, ack function,
|   http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.TerminationChecker
| szép példa az osztás Andreas Abel levelében (irrelevant params)
| 
| recordok nagyon jól jönnének _≡_-nél, megmutatni, hogy milyen szép struktúrába lehet rendezni a dolgokat
| data Negyzetgyok : ℕ -> ℕ -> Set where
|   c : {n : ℕ} -> n -> Negyzetgyok n (n * n)
| primitív rekurzió?
| fejezetek végén, hogy mit hol lehet találni a standard könyvtárban
| típusosztályok: agda-mailing list: something like type classes in agda
| miért kell a Set1, Set2 stb.: Russel paradoxont megmutatni; Conor blogbejegyzés
| miért kell megadni a típusokat mindig?
| uscs-es jegyzetek anyagai
| Peti txt-jét beegyesíteni
| így kell lefordítani Agda programokat: "If you set the include path manually, then the current directory is not"
| SortedList: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Irrelevance
| binaris szamokat unarissa konvertalni stb
| ffi konyvtarban ki kell adni egy cabal installt az FFI mukodesehez
| motivationben "Program Analysis"-t megemliteni (wikipedian info)
| coinduction innét: http://www.cse.chalmers.se/~nad/publications/danielsson-altenkirch-subtyping.html
|         meg innét: http://www.cs.nott.ac.uk/~txa/g53cfr/
| russel-paradoxont posztulálni, belátni bármit

| BEADANDÓ ÖTLETEK
| ----------------
| 
| egész számokat szépen kidolgozni (Agda stdlib nélkül) bebiz. gyűrű
| modulo n maradékosztályok
| ORSI modellezése
| monad law-kat betartó monad implementáció
| type checker for lambda calculus
| power of pi-ben levő adatbázisos/másik példa kidolgozása Agdában
| konstruktiv vs indirekt bizonyitas peldat kidolgozni, pl. sqrt(2)^sqrt(2) irrac.
| JS backenddel valamit
| parser, alge3brai kif.
| racionális számok, valós számok valamely alakja
| polinomok, gyöktényezős alak stb., többhatározatlanú polinomok
| bebiz., hogy x és diszj.unió gyűrűt alkotnak
