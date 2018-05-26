# Initial Categories with Families

This repository contains the developments of a formalization of categories with families (CwFs) defined as a generalized algebraic theory described in [Internal Type Theory](http://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf). This was a master's thesis and the final report is also available.

There are three different CwFs implemented so far; those are: unityped, simply typed, and the full CwFs that model dependent types. Extra structure is added to acquire models of the corresponding lambda calculus.

We consider the category of CwFs for each version and define objects and morphisms. After, we build two term models: one with explicit substitutions and one with implicit. Morphisms are defined between those with the purpose of demonstrating an isomorphism of the term models. 

This should be an isomorphism of initial CwFs, although proofs of initiality are not formalized.

# Content

The structure is as follows:

* __Unityped/__

    Unityped CwFs with extra structure.
    
* __SimpTyped/__
    
    Intrinsic simply typed CwFs with extra structure.
    
* __ExtSimpTyped/__

    Extrinsic simply typed CwFs with extra structure.
    
* __ExtDepTyped/__

    Extrinsic full CwFs with Pi types and universe a la Russell.

This is a work in progress; there are some unfinished definitions, especially for the dependently typed developments.
