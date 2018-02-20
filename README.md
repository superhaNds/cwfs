# Categories with Families as a model of lambda calculus

This repository contains the developments of a formalization of categories with
families described as a generalized algebraic theory described in [Internal Type Theory](http://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf)
and the traditional notions of lambda calculus it models.

We consider the category of CwFs starting with the unityped version where types are removed 
and we define what it means to be an object in the category. After, we build two term models
one with explicit substitutions and one with implicit with ordinary lambda terms and construct
CwF morphisms between them and an isomorphism. This work is performed for untyped, simply
typed (two parts), and some formulation of a full CwF.

# Content

The structure is as follows:

* __Unityped/__

    Unityped CwFs and untyped lambda calculus.
    
* __SimpTyped/__
    
    Intrinsically simply typed CwFs and lambda calculus.
    
* __Ext-Typed/__

    Extrinsically simply typed CwFs and lambda calculus, i.e., raw terms with external typing relations. And an extrinsic dependently typed lambda calculus and CwF with Pi and U ala Russel. 
