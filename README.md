# Initial Categories with Families

This repository contains the developments of a formalization of categories with
families (CwFs) defined as a generalized algebraic theory described in [Internal Type Theory](http://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf)

There are three versions of CwFs we work with, unityped, simply typed, and the full CwFs 
that model dependent types. Extra structure is added to have a complete model of
lambda calculus.

We consider the category of CwFs for each version and define objects and morphisms.
After, we build two term models: one with explicit substitutions and one with implicit.
Morphisms are defined between those two term models and we construct an isomorphism. 
This should be an isomorphism of initial CwFs.

# Content

The structure is as follows:

* __Unityped/__

    Unityped CwFs with extra structure and untyped lambda calculus.
    
* __SimpTyped/__
    
    Intrinsic simply typed CwFs with extra structure and simply typed lambda calculus.
    
* __ExtSimpTyped/__

    Extrinsic simply typed CwFs with extra structure.
    
* __ExtDepTyped/__

    Extrinsic full CwFs with Pi types and universe a la Russell.

It is a work in progress, there are some unfinished definitions, especially for the dependently typed
developments.     
