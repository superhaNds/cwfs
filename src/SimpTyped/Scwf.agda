-----------------------------------------------------------------------------------------
-- The notions of simply typed categories with families as records. The base Scwf which
-- essentially represents a theory of simply typed n-place functions. And second, the
-- λβη-scwf encapsulates a simply typed lambda calculus up to beta and eta.
-- The formulation is well-scoped, i.e., contexts are indexed by length.
-----------------------------------------------------------------------------------------
module SimpTyped.Scwf where

open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary

record Scwf : Set₁ where
  infix 4 _~_
  infix 4 _≈_
  infix 8 _∘_
  field

    Ty  : Set
    Ctx : Nat → Set
    Tm  : ∀ {n} → Ctx n → Ty → Set
    Sub : ∀ {m n} → Ctx m → Ctx n → Set

    ⋄   : Ctx zero
    _∙_ : ∀ {n} → Ctx n → Ty → Ctx (suc n)
    
    _~_ : ∀ {n A} {Γ : Ctx n}             (_ _ : Tm Γ A)  → Set
    _≈_ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (_ _ : Sub Γ Δ) → Set

    IsEquiv~ : ∀ {n A} {Γ : Ctx n}             → IsEquivalence (_~_ {A = A} {Γ})
    IsEquiv≈ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → IsEquivalence (_≈_ {Δ = Δ} {Γ})

    -- cwf operators

    id : ∀ {n} {Γ : Ctx n} → Sub Γ Γ
    
    _∘_ : ∀ {k m n} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
          → Sub Γ Θ
          → Sub Δ Γ
          → Sub Δ Θ
            
    _[_] : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n}
           → Tm Γ A
           → Sub Δ Γ
           → Tm Δ A
    
    <> : ∀ {n} {Γ : Ctx n} → Sub Γ ⋄
    
    <_,_> : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n}
            → Sub Γ Δ
            → Tm Γ A
            → Sub Γ (Δ ∙ A)
    
    p : ∀ {n A} {Γ : Ctx n} → Sub (Γ ∙ A) Γ
    q : ∀ {n A} {Γ : Ctx n} → Tm (Γ ∙ A) A

    -- cwf axioms
 
    id-zero : id {Γ = ⋄} ≈ <>

    left-zero : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → <> ∘ γ ≈ <>

    idExt : ∀ {n A} {Γ : Ctx n} → id {Γ = Γ ∙ A} ≈ < p , q >

    idL : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → id ∘ γ ≈ γ
    
    idR : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Γ Δ} → γ ∘ id ≈ γ

    assoc : ∀ {j k m n} {Λ : Ctx j} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
              (γ : Sub Γ Θ) (δ : Sub Δ Γ) (ζ : Sub Λ Δ)
            → (γ ∘ δ) ∘ ζ ≈ γ ∘ (δ ∘ ζ)

    subId : ∀ {n A} {Γ : Ctx n} {t : Tm Γ A} → t [ id ] ~ t

    pCons : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t : Tm Γ A} (γ : Sub Γ Δ) → p ∘ < γ , t > ≈ γ

    qCons : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t : Tm Γ A} (γ : Sub Γ Δ) → q [ < γ , t > ] ~ t

    subComp : ∀ {k m n A} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
                (t : Tm Θ A) {γ : Sub Γ Θ} {δ : Sub Δ Γ}
              → t [ γ ∘ δ ] ~ t [ γ ] [ δ ]
                      
    compExt : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t : Tm Δ A} {γ : Sub Δ Γ} {δ : Sub Γ Δ}
              →  < γ , t > ∘ δ ≈ < γ ∘ δ , t [ δ ] >

    -- closed under congruence

    cong-sub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t t' : Tm Γ A} {γ γ' : Sub Δ Γ}
               → t ~ t'
               → γ ≈ γ'
               →  t [ γ ] ~ t' [ γ' ]
               
    cong-<,> : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t t' : Tm Δ A} {γ γ' : Sub Δ Γ}
               → t ~ t'
               → γ ≈ γ'
               → < γ , t > ≈ < γ' , t' >
               
    cong-∘ : ∀ {k m n} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
               {γ δ : Sub Γ Θ} {γ' δ' : Sub Δ Γ}
             → γ ≈ δ
             → γ' ≈ δ'
             → γ ∘ γ' ≈ δ ∘ δ'

  setoid~ : ∀ {n A} {Γ : Ctx n} → Setoid _ _
  setoid~ {A = A} {Γ} = record { isEquivalence = IsEquiv~ {A = A} {Γ} }

  setoid≈ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → Setoid _ _
  setoid≈ {Δ = Δ} {Γ} = record { isEquivalence = IsEquiv≈ {Δ = Δ} {Γ} }

  -- lifting

  ⇑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub Δ Γ) → Sub (Δ ∙ A) (Γ ∙ A)
  ⇑ γ = < γ ∘ p , q >

  -- weakening a term

  ⁺_ : ∀ {n A B} {Γ : Ctx n} → Tm Γ A → Tm (Γ ∙ B) A
  ⁺_ = _[ p ]

-- Extra structure is added: lambdas, application, function type.

record λβη-Scwf : Set₁ where
  field
    scwf : Scwf
    
  open Scwf scwf public

  field

    -- function type
    
    _`→_ : Ty → Ty → Ty
    
    -- lambda abstractions and application
    
    lam : ∀ {n A B} {Γ : Ctx n}
          → Tm (Γ ∙ A) B
          → Tm Γ (A `→ B)
          
    app : ∀ {n A B} {Γ : Ctx n}
          → Tm Γ (A `→ B)
          → Tm Γ A
          → Tm Γ B

    -- substituting under application and lambda
    
    subApp : ∀ {m n A B} {Δ : Ctx m} {Γ : Ctx n}
               {t : Tm Γ (A `→ B)} {u : Tm Γ A} {γ : Sub Δ Γ}
             → app (t [ γ ]) (u [ γ ]) ~ (app t u) [ γ ] 
             
    subLam : ∀ {m n A B} {Δ : Ctx m} {Γ : Ctx n}
               {t : Tm (Γ ∙ A) B} {γ : Sub Δ Γ}
             → lam t [ γ ] ~ lam (t [ < γ ∘ p , q > ])

    -- beta and eta equalities

    beta : ∀ {n A B} {Γ : Ctx n} {t : Tm (Γ ∙ A) B} {u}
           → app (lam t) u ~ t [ < id , u > ]
        
    eta : ∀ {n A B} {Γ : Ctx n} {t : Tm Γ (A `→ B)}
          → lam (app (t [ p ]) q) ~ t 

    -- congruence rules
    
    cong-lam : ∀ {n A B} {Γ : Ctx n} {t t' : Tm (Γ ∙ A) B}
               → t ~ t'
               → lam t ~ lam t'
             
    cong-app : ∀ {n A B} {Γ : Ctx n} {t t' : Tm Γ (A `→ B)} {u u'}
               → t ~ t'
               → u ~ u'
               → app t u ~ app t' u'


