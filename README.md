# Categories with Families as a model of lambda calculus

This repository contains the developments of a formalization of categories with
families described as a generalized algebraic theory described in [Internal Type Theory](http://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf)
and the traditional notions of lambda calculus it models.

We consider the category of CwFs starting with the unityped version where types are removed 
and we define what it means to be a CwF object in this category. After, we build an explicit 
calculus and the corresponding traditional lambda calculus that with substitution and operations
formalized in the meta-language. We implement formal proofs that  lambda calculus is a Unityped 
CwF object and then we show that it is isomorphic to the explicit CwF object. The motivation 
behind the idea is to construct initial objects in the CwF category.

We build the model theory of the lambda calculus for the untyped, simply typed, and some parts 
of depedently typed formulations.

# Content

The structure is as follows:

* __Unityped/__

    Unityped CwFs and untyped lambda calculus.
    
* __SimpTyped/__
    
    Intrinsically simply typed CwFs and lambda calculus.
    
* __Ext-Typed/__

    Extrinsically simply typed CwFs and lambda calculus, i.e., raw terms with external typing relations. And an extrinsic dependently typed lambda calculus and CwF with Pi and U ala Russel. 
