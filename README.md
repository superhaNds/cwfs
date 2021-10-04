# Initial Categories with Families

This repository contains the developments of a formalization of categories with families (CwFs) defined as a generalized algebraic theory described in [Internal Type Theory](http://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf). This was a master's thesis and the final report is also available [here](https://odr.chalmers.se/bitstream/20.500.12380/255039/1/255039.pdf).
The code has been changed profoundly since the time of writing though.

There are three different CwFs implemented so far; those are: unityped, simply typed, and some part of a full CwFs construct that models dependent types. Extra structure is added to acquire models of the corresponding lambda calculus.

We consider the category of CwFs for each version and define objects and morphisms. After, we build two term models: one with explicit substitutions and one with implicit. Morphisms are defined between those with the purpose of demonstrating an isomorphism of the term models. 
Apart from this, we have an isomorphism between extrinsically typed and intrinsically typed simply typed cwfs.

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

## 10/2021 Update: 
1. Finished better simply typed version using well scoped contexts-terms.
2. Made compatible with standard library version 1.7 and tested with agda 2.6.2.