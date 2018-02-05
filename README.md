# Categories with Families as a model of lambda calculus

This repository contains the developments of a formalization of categories with
families described as a generalized algebraic theory and the traditional notions
of lambda calculus it models.

We consider the category of CwFs starting with the unityped version where there are
no types and we define what it means to be a CwF object in this category. After, we
build an explicit calculus and the corresponding traditional lambda calculus that with
substitution and operations formalized in the meta-language. We implement formal proofs that 
lambda calculus is a Unityped CwF object and then we show that it is isomorphic to the
explicit CwF object. The motivation behind the idea is to construct initial objects 
in the category.

We build the model theory of the lambda calculus from untyped, simply typed, and some parts of depdently typed formulations.

# Content

The structure is as follows:

* __Unityped/__

    Unityped CwFs and untyped lambda calculus.
    
* __SimpTyped/__
    
    Intrinsically Simply typed CwFs and simply typed lambda calculus.
    
* __Ext-Typed__

    Extrnsinc simply typed CwFs and lambda calculus, i.e., raw terms with external typing relations. And an extrinsic dependently typed lambda calculus with Pi and U ala Russel. 
