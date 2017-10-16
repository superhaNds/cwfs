module Unityped.Ucwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary

record Ucwf : Set₁ where
  infix 9 _∘_
  field
    Term   : Nat → Set
    Hom    : Nat → Nat → Set
    id     : (ν : Nat) → Hom ν ν
    <>     : {μ : Nat} → Hom μ 0
    p      : (ν : Nat) → Hom (suc ν) ν
    q      : {ν : Nat} → Term (suc ν)
    _∘_    : {μ ν k : Nat} → Hom ν k → Hom μ ν → Hom μ k
    _[_]   : {μ ν : Nat} → Term ν → Hom μ ν → Term μ
    <_,_>  : {μ ν : Nat} → Hom μ ν → Term μ → Hom μ (suc ν)

    id₀   : id 0 ≡ <>
    ∘<>   : ∀ {μ ν : Nat} (ts : Hom μ ν) → <> ∘ ts ≡ <> 
    varp  : ∀ {ν : Nat} → id (suc ν) ≡ < p ν , q >
    idL   : ∀ {μ ν : Nat} (ts : Hom μ ν) → id ν ∘ ts ≡ ts
    idR   : ∀ {μ ν : Nat} (ts : Hom μ ν) → ts ∘ id μ ≡ ts
    assoc : ∀ {μ ν k p : Nat} (ts : Hom ν k) (us : Hom μ ν) (vs : Hom p μ) →
             (ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)
    terId : ∀ {μ ν : Nat} (t : Term ν) → t [ id ν ] ≡ t
    pCons : ∀ {μ ν k : Nat} → (t : Term ν) → (ts : Hom ν k) → p k ∘ < ts , t > ≡ ts
    qCons : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν μ) → q [ < ts , t > ] ≡ t
    clos  : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν ν) (us : Hom μ ν) →
             t [ ts ∘  us ] ≡ t [ ts ] [ us ]
    maps  : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν μ) (us : Hom μ ν) →
             < ts , t > ∘ us ≡ < ts ∘ us , t [ us ] >
  
  ⇑ : ∀ {m n} (ts : Hom m n) → Hom (suc m) (suc n)
  ⇑ ts = < ts ∘ p _ , q >
  
record λ-app-ucwf : Set₁ where
  infix 10 _·_
  field
    ucwf : Ucwf
    
  open Ucwf ucwf public
  
  field
    ƛ   : {ν : Nat} → Term (suc ν) → Term ν
    _·_ : {ν : Nat} → Term ν → Term ν → Term ν

record λβ-ucwf : Set₁ where
  field
    λ-$-ucwf : λ-app-ucwf

  open λ-app-ucwf λ-$-ucwf public

  -- field
    -- β   : {ν : Nat} (t : Term (suc ν)) (u : Term ν) → (ƛ t · u) ≈ (t [ < id ν , u > ])
  --  η   : {ν : Nat} (t : Term ν) → ƛ (t [ p ν ] · q) ~ t
  --  app : {ν μ : Nat} (t u : Term ν) (ts : Hom μ ν) → ((t [ ts ]) · (u [ ts ])) ~ ((t · u) [ ts ])
  --  abs : {ν μ : Nat} (t : Term (suc ν)) (ts : Hom μ ν) → (ƛ t [ ts ]) ~ (ƛ (t [ ⇑ ts ]))
