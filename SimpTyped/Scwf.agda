----------------------------------------------------------------------------
-- The notion of an intrinsically typed simply typed category with families
-- as a generalized algebraic theory. An extension includes lambda and apply
-- In this formulation, contexts are just list of types, so the length
-- is not kept.
----------------------------------------------------------------------------
module SimpTyped.Scwf where

open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary
----------------------------------------------------------------------------
-- pure scwf that is directly typed

record Scwf : Set₁ where
  infix 4 _~_
  infix 4 _~~_
  infix 8 _∘_
  field

    -- sorts
    Ty  : Set
    Ctx : Set
    Tm  : Ctx → Ty → Set
    Hom : Ctx → Ctx → Set

    -- empty context and cons
    ε   : Ctx
    _,_ : Ctx → Ty → Ctx
    
    _~_  : ∀ {Γ α} → Rel (Tm Γ α) lzero
    _~~_ : ∀ {Γ Δ} → Rel (Hom Γ Δ) lzero
    -- ~-Equiv : ∀ {Γ α} → IsEquivalence (_~_ {Γ} {α})
    -- ~~-Equiv : ∀ {Γ Δ} → IsEquivalence (_~~_ {Γ} {Δ})

    -- operators    
    <>    : ∀ {Γ}     → Hom Γ ε
    id    : ∀ {Γ}     → Hom Γ Γ
    p     : ∀ {Γ α}   → Hom (Γ , α) Γ
    q     : ∀ {Γ α}   → Tm (Γ , α) α
    _∘_   : ∀ {Γ Δ Θ} → Hom Γ Θ → Hom Δ Γ → Hom Δ Θ
    _[_]  : ∀ {Γ Δ α} → Tm Γ α  → Hom Δ Γ → Tm Δ α
    <_,_> : ∀ {Γ Δ α} → Hom Γ Δ → Tm Γ α  → Hom Γ (Δ , α)

    -- cwf laws
    id₀   : id {ε} ~~ <>
    
    ∘<>   : ∀ {Γ Δ} (γ : Hom Γ Δ) →
             <> ∘ γ ~~ <>
    
    varp  : ∀ {Γ α} →
             id {Γ , α} ~~ < p , q >
    
    idL   : ∀ {Γ Δ} (γ : Hom Δ Γ) →
             id ∘ γ ~~ γ
    
    idR   : ∀ {Γ Δ} (γ : Hom Γ Δ) →
             γ ∘ id ~~ γ
    
    assoc : ∀ {Γ Δ Θ Λ} (γ : Hom Δ Θ) (δ : Hom Γ Δ) (ζ : Hom Λ Γ) →
             (γ ∘ δ) ∘ ζ ~~ γ ∘ (δ ∘ ζ)
            
    tmId  : ∀ {Γ α} (t : Tm Γ α) →
             t [ id ] ~ t
    
    pCons : ∀ {Δ Θ α} (t : Tm Δ α) (γ : Hom Δ Θ) →
             p ∘ < γ , t > ~~ γ
    
    q[]   : ∀ {Γ Δ α} (t : Tm Γ α) (γ : Hom Γ Δ) →
             q [ < γ , t > ] ~ t
    
    clos  : ∀ {Γ Δ Θ α} (t : Tm Δ α) (γ : Hom Γ Δ) (δ : Hom Θ Γ) →
             t [ γ ∘ δ ] ~ t [ γ ] [ δ ]
            
    maps  : ∀ {Γ Δ α} (t : Tm Δ α) (γ : Hom Δ Γ) (δ : Hom Γ Δ) →
             < γ , t > ∘ δ ~~ < γ ∘ δ , t [ δ ] >
            
    cong-[] : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Hom Δ Γ} →
               t ~ t' →
               γ ~~ γ' →
               t [ γ ] ~ t' [ γ' ]
               
    cong-<,> : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Hom Γ Δ} →
                t ~ t' →
                γ ~~ γ' →
                < γ , t > ~~ < γ' , t' >
               
    cong-∘ : ∀ {Γ Δ Θ} {γ δ : Hom Δ Θ} {γ' δ' : Hom Γ Δ} →
              γ ~~ δ →
              γ' ~~ δ' →
              γ ∘ γ' ~~ δ ∘ δ'

  weaken : ∀ {Γ α} → Tm Γ α → Tm (Γ , α) α
  weaken = _[ p ]

record Lambda-scwf : Set₁ where
  infix 10 _·_

  field scwf : Scwf
  open Scwf scwf public

  field

    -- Function types
    _`→_ : Ty → Ty → Ty

    -- lambda terms and apply
    ƛ   : ∀ {Γ α β} → Tm (Γ , α) β → Tm Γ (α `→ β)
    _·_ : ∀ {Γ α β} → Tm Γ (α `→ β) → Tm Γ α → Tm Γ β

    -- substituting an application and lambda
    appCm : ∀ {Γ Δ α β} (t : Tm Γ (α `→ β)) (u : Tm Γ α) (γ : Hom Δ Γ) →
             (t · u) [ γ ]  ~ (t [ γ ]) · (u [ γ ])
            
    lamCm : ∀ {Γ Δ α β} (t : Tm (Γ , α) β) (γ : Hom Δ Γ) →
             ƛ t [ γ ] ~ ƛ (t [ < γ ∘ p , q > ])

    -- congruence rules
    cong-ƛ : ∀ {Γ α β} {t t' : Tm (Γ , α) β} →
              t ~ t' →
              ƛ t ~ ƛ t'
             
    cong-· : ∀ {Γ α β} {t t' : Tm Γ (α `→ β)} {u u' : Tm Γ α} →
              t ~ t' →
              u ~ u' →
              t · u ~ t' · u'

record Lambda-β-scwf : Set₁ where
  field
    lambda-scwf : Lambda-scwf
  open Lambda-scwf lambda-scwf public
  -- η : {n : Nat} (t : Term n) → ƛ (weaken t · q) ~ t
  field
    β : ∀ {Γ α β}
          (t : Tm (Γ , α) β)
          (u : Tm Γ α) →
        ƛ t · u ~ t [ < id , u > ]
