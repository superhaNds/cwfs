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
    id     : {n : Nat} → Hom n n
    <>     : {m : Nat} → Hom m 0
    p      : {n : Nat} → Hom (suc n) n
    q      : {n : Nat} → Term (suc n)
    _∘_    : {m n k : Nat} → Hom n k → Hom m n → Hom m k
    _[_]   : {m n : Nat} → Term n → Hom m n → Term m
    <_,_>  : {m n : Nat} → Hom m n → Term m → Hom m (suc n)

    -- axioms
    id₀   : id {0} ~ₕ <>
    ∘<>   : ∀ {m n : Nat} (ts : Hom m n) → <> ∘ ts ~ₕ <> 
    varp  : ∀ {n : Nat} → id {suc n} ~ₕ < p , q >
    idL   : ∀ {m n : Nat} (ts : Hom m n) → id ∘ ts ~ₕ ts
    idR   : ∀ {m n : Nat} (ts : Hom m n) → ts ∘ id ~ₕ ts
    assoc : ∀ {m n κ ι : Nat} (ts : Hom n κ) (us : Hom m n) (vs : Hom ι m) →
             (ts ∘ us) ∘ vs ~ₕ ts ∘ (us ∘ vs)
    terId : ∀ {m n : Nat} (t : Term n) → t [ id ] ~ₜ t
    pCons : ∀ {m n κ : Nat} → (t : Term n) → (ts : Hom n κ) → p ∘ < ts , t > ~ₕ ts
    qCons : ∀ {m n : Nat} (t : Term n) (ts : Hom n m) → q [ < ts , t > ] ~ₜ t
    clos  : ∀ {m n κ : Nat} (t : Term n) (ts : Hom m n) (us : Hom κ m) →
             t [ ts ∘  us ] ~ₜ t [ ts ] [ us ]
    maps  : ∀ {m n : Nat} (t : Term n) (ts : Hom n m) (us : Hom m n) →
             < ts , t > ∘ us ~ₕ < ts ∘ us , t [ us ] >
             
    -- congruence rules for operators
    cong-<,> : ∀ {m n} {t u : Term m} {ts us : Hom m n} →
                t ~ₜ u → ts ~ₕ us → < ts , t > ~ₕ < us , u >
    cong-[_] : ∀ {m n} {t u : Term n} {ts us : Hom m n} →
                t ~ₜ u → ts ~ₕ us → t [ ts ] ~ₜ u [ us ]
    cong-∘   : ∀ {m n k} {ts vs : Hom n k} {us zs : Hom m n} →
                ts ~ₕ vs → us ~ₕ zs → ts ∘ us ~ₕ vs ∘ zs
  
  ⇑ : ∀ {m n} (ts : Hom m n) → Hom (suc m) (suc n)
  ⇑ ts = < ts ∘ p , q >

  weaken : ∀ {m} → Term m → Term (suc m)
  weaken {m} = _[ p ] 

-- Extending the pure ucwf with lambdas and applications

record Lambda-ucwf : Set₁ where
  infix 10 _·_ 
  field
    ucwf : Ucwf   
  open Ucwf ucwf public  
  field
    ƛ   : {n : Nat} → Term (suc n) → Term n
    _·_ : {n : Nat} → Term n → Term n → Term n
    cong-ƛ : ∀ {n} {t u : Term (suc n)} → t ~ₜ u → ƛ t ~ₜ ƛ u
    cong-· : ∀ {n} {t u t′ u′ : Term n} → t ~ₜ t′ → u ~ₜ u′ → t · u ~ₜ t′ · u′
    app : {n m : Nat} (t u : Term n) (ts : Hom m n) → (t [ ts ]) · (u [ ts ]) ~ₜ (t · u) [ ts ]
    abs : {n m : Nat} (t : Term (suc n)) (ts : Hom m n) → ƛ t [ ts ] ~ₜ ƛ (t [ ⇑ ts ])

-- Extending the ucwf with lambdas up to β and η

record Lambda-βη-ucwf : Set₁ where
  field
    lambda-ucwf : Lambda-ucwf

  open Lambda-ucwf lambda-ucwf public

  field
    β   : {n : Nat} (t : Term (suc n)) (u : Term n) → ƛ t · u ~ₜ t [ < id , u > ]
    η   : {n : Nat} (t : Term n) → ƛ (weaken t · q) ~ₜ t
    
