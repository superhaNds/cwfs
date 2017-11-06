-----------------------------------------------------------------------------
-- The notion of a ucwf and its extensions with lambdas and others
-----------------------------------------------------------------------------
module Unityped.Ucwf where

open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary

-----------------------------------------------------------------------------
-- The sorts, operator symbols, and axioms of a ucwf gathered as a record

record Ucwf : Set₁ where
  infix 4 _~ₜ_
  infix 4 _~ₕ_
  infix 9 _∘_
  
  field
    -- the types for terms and substitutions 
    Term   : Nat → Set
    Hom    : Nat → Nat → Set

    -- two relations regarding equality of terms and substitutions
    _~ₜ_   : ∀ {n} → Rel (Term n) lzero
    _~ₕ_   : ∀ {m n} → Rel (Hom m n) lzero

    -- operator symbols
    id     : (ν : Nat) → Hom ν ν
    <>     : {μ : Nat} → Hom μ 0
    p      : (ν : Nat) → Hom (suc ν) ν
    q      : {ν : Nat} → Term (suc ν)
    _∘_    : {μ ν k : Nat} → Hom ν k → Hom μ ν → Hom μ k
    _[_]   : {μ ν : Nat} → Term ν → Hom μ ν → Term μ
    <_,_>  : {μ ν : Nat} → Hom μ ν → Term μ → Hom μ (suc ν)

    -- axioms
    id₀   : id 0 ~ₕ <>
    ∘<>   : ∀ {μ ν : Nat} (ts : Hom μ ν) → <> ∘ ts ~ₕ <> 
    varp  : ∀ {ν : Nat} → id (suc ν) ~ₕ < p ν , q >
    idL   : ∀ {μ ν : Nat} (ts : Hom μ ν) → id ν ∘ ts ~ₕ ts
    idR   : ∀ {μ ν : Nat} (ts : Hom μ ν) → ts ∘ id μ ~ₕ ts
    assoc : ∀ {μ ν κ ι : Nat} (ts : Hom ν κ) (us : Hom μ ν) (vs : Hom ι μ) →
             (ts ∘ us) ∘ vs ~ₕ ts ∘ (us ∘ vs)
    terId : ∀ {μ ν : Nat} (t : Term ν) → t [ id ν ] ~ₜ t
    pCons : ∀ {μ ν κ : Nat} → (t : Term ν) → (ts : Hom ν κ) → p κ ∘ < ts , t > ~ₕ ts
    qCons : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν μ) → q [ < ts , t > ] ~ₜ t
    clos  : ∀ {μ ν κ : Nat} (t : Term ν) (ts : Hom μ ν) (us : Hom κ μ) →
             t [ ts ∘  us ] ~ₜ t [ ts ] [ us ]
    maps  : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν μ) (us : Hom μ ν) →
             < ts , t > ∘ us ~ₕ < ts ∘ us , t [ us ] >
             
    -- congruence rules for operators
    cong-<,> : ∀ {m n} {t u : Term m} {ts us : Hom m n} →
                t ~ₜ u → ts ~ₕ us → < ts , t > ~ₕ < us , u >
    cong-[_] : ∀ {m n} {t u : Term n} {ts us : Hom m n} →
                t ~ₜ u → ts ~ₕ us → t [ ts ] ~ₜ u [ us ]
    cong-∘   : ∀ {m n k} {ts vs : Hom n k} {us zs : Hom m n} →
                ts ~ₕ vs → us ~ₕ zs → ts ∘ us ~ₕ vs ∘ zs
  
  ⇑ : ∀ {m n} (ts : Hom m n) → Hom (suc m) (suc n)
  ⇑ ts = < ts ∘ p _ , q >

  weaken : ∀ {m} → Term m → Term (suc m)
  weaken {m} = _[ p m ] 

-- Extending the pure ucwf with lambdas and applications

record Lambda-ucwf : Set₁ where
  infix 10 _·_
  
  field
    ucwf : Ucwf
    
  open Ucwf ucwf public
  
  field
    ƛ   : {ν : Nat} → Term (suc ν) → Term ν
    _·_ : {ν : Nat} → Term ν → Term ν → Term ν
    app : {ν μ : Nat} (t u : Term ν) (ts : Hom μ ν) → (t [ ts ]) · (u [ ts ]) ~ₜ (t · u) [ ts ]
    abs : {ν μ : Nat} (t : Term (suc ν)) (ts : Hom μ ν) → ƛ t [ ts ] ~ₜ ƛ (t [ ⇑ ts ])

-- Extending the ucwf with lambdas up to β and η

record Lambda-βη-ucwf : Set₁ where
  field
    lambda-ucwf : Lambda-ucwf

  open Lambda-ucwf lambda-ucwf public

  field
    β   : {ν : Nat} (t : Term (suc ν)) (u : Term ν) → ƛ t · u ~ₜ t [ < id ν , u > ]
    η   : {ν : Nat} (t : Term ν) → ƛ (weaken t · q) ~ₜ t
    
