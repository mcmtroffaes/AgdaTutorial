% Introduction to Agda

\begin{code}
module Index_a where

a = Set --
\end{code}


[Motivation](Motivation_a.xml)

[Technical Information](Technical_Info_a.xml)

Data Sets
:   [Bool](Bool_a.xml) | [ℕ](Nat_a.xml) | [List](List_a.xml) | [Product](Product_a.xml) | [Union](Union_a.xml) | [Exercises](DataSetsExercises_a.xml)
Predicates 
:   [≤](LessThan_a.xml) | [Equality](Equality_a.xml) | [Even, Odd](Even_a.xml) | [Elem](Elem_a.xml) | [Sublist](Sublist_a.xml)
Subsets
:   [Vec](Vec_a.xml) | [Fin](Fin_a.xml) | [Sigma](Sigma_a.xml)
Views
:   [Parity](Parity_a.xml) | [Ordering](Ordering_a.xml) | [Dec](Dec_a.xml)
Algebraic Data Structures
:   Group | Ring | ...

Coinduction
[Logic](Logic_a.xml)



| talk about agda termination check, ack function,
|   http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.TerminationChecker
| lásd még proba.agda
| szép példa az osztás Andreas Abel levelében (irrelevant params)

| recordok nagyon jól jönnének _≡_-nél, megmutatni, hogy milyen szép struktúrába lehet rendezni a dolgokat

| beadandók: pl. egész számokat szépen kidolgozni (Agda stdlib nélkül) bebiz. gyűrű
|                modulo n maradékosztályok
|                ORSI modellezése
|                monad law-kat betartó monad implementáció
|                type checker for lambda calculus
|                power of pi-ben levő adatbázisos/másik példa kidolgozása Agdában
|                konstruktiv vs indirekt bizonyitas peldat kidolgozni, pl. sqrt(2)^sqrt(2) irrac.
|                JS backenddel valamit
|                parser, alge3brai kif.
|                racionális számok, valós számok valamely alakja
|                polinomok
|
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

| dependent type-ok előtt egy újabb motiváció ezekről, logikai bevezetővel kb. ami Motivation2-ben van

| binaris szamokat unarissa konvertalni stb
| ffi konyvtarban ki kell adni egy cabal installt az FFI mukodesehez
| motivationben "Program Analysis"-t megemliteni (wikipedian info)
| coinduction innét: http://www.cse.chalmers.se/~nad/publications/danielsson-altenkirch-subtyping.html

| leírásba: ghc-t path-ba (C:\Program Files\Haskell Platform\2011.2.0.1\bin) + .emacs-ot lehet, hogy nem olvassa be az emacs, ezt kideríteni + haskell-mode-ot telepíteni, fileokat site-lisp-be (C:\Program Files\Emacs\site-lisp)
| russel-paradoxont posztulálni, belátni bármit
| windowsba fontok
| coinduction material: http://www.cs.nott.ac.uk/~txa/g53cfr/
| .emacs file helye: Users/usernév/AppData/Roaming/.emacs
| normalize és deduce type bill.kombinációja
|

