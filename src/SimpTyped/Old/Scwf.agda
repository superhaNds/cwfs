----------------------------------------------------------------------------
-- The notion of an intrinsically typed simply typed category with families
-- as a generalized algebraic theory. An extension includes lambda and apply
-- In this formulation, contexts are just list of types, so the length
-- is not kept.
----------------------------------------------------------------------------
module SimpTyped.Old.Scwf where

open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary
----------------------------------------------------------------------------
-- pure scwf that is directly typed

record Scwf : Set₁ where
  infix 4 _≈_
  infix 4 _≋_
  infix 8 _∘_
  field

    -- sorts i.e., types, contexts, terms, and substitutions
    
    Ty  : Set
    Ctx : Set
    Tm  : Ctx → Ty → Set
    Sub : Ctx → Ctx → Set

    -- empty context and context extension
    -- ε is the terminal object of the base category
    
    ⋄   : Ctx
    _∙_ : Ctx → Ty → Ctx
    
    _≈_  : ∀ {Γ α} → Rel (Tm Γ α) lzero
    _≋_ : ∀ {Γ Δ} → Rel (Sub Γ Δ) lzero

    IsEquivT : ∀ {Γ α} → IsEquivalence (_≈_ {Γ} {α})
    IsEquivS : ∀ {Γ Δ} → IsEquivalence (_≋_ {Γ} {Δ})

    -- operators    
    
    id    : ∀ {Γ}     → Sub Γ Γ
    _∘_   : ∀ {Γ Δ Θ} → Sub Γ Θ → Sub Δ Γ → Sub Δ Θ
    _[_]  : ∀ {Γ Δ α} → Tm Γ α  → Sub Δ Γ → Tm Δ α
    <>    : ∀ {Γ}     → Sub Γ ⋄
    <_,_> : ∀ {Γ Δ α} → Sub Γ Δ → Tm Γ α  → Sub Γ (Δ ∙ α)
    p     : ∀ {Γ α}   → Sub (Γ ∙ α) Γ
    q     : ∀ {Γ α}   → Tm (Γ ∙ α) α
   
    -- cwf laws
    
    id₀ : id {⋄} ≋ <>
    
    left-zero : ∀ {Γ Δ} (γ : Sub Γ Δ) → <> ∘ γ ≋ <>
    
    idExt : ∀ {Γ α} → id {Γ ∙ α} ≋ < p , q >
    
    idL : ∀ {Γ Δ} (γ : Sub Δ Γ) → id ∘ γ ≋ γ
    
    idR : ∀ {Γ Δ} (γ : Sub Γ Δ) → γ ∘ id ≋ γ
    
    assoc : ∀ {Γ Δ Θ Λ} (γ : Sub Δ Θ) (δ : Sub Γ Δ) (ζ : Sub Λ Γ)
            → (γ ∘ δ) ∘ ζ ≋ γ ∘ (δ ∘ ζ)
            
    subId : ∀ {Γ α} (t : Tm Γ α) → t [ id ] ≈ t
    
    pCons : ∀ {Γ Δ α} (t : Tm Γ α) (γ : Sub Γ Δ) → p ∘ < γ , t > ≋ γ
    
    qCons : ∀ {Γ Δ α} (t : Tm Γ α) (γ : Sub Γ Δ) → q [ < γ , t > ] ≈ t
    
    subComp : ∀ {Γ Δ Θ α} (t : Tm Δ α) (γ : Sub Γ Δ) (δ : Sub Θ Γ)
              → t [ γ ∘ δ ] ≈ t [ γ ] [ δ ]
            
    compExt : ∀ {Γ Δ α} (t : Tm Δ α) (γ : Sub Δ Γ) (δ : Sub Γ Δ)
              →  < γ , t > ∘ δ ≋ < γ ∘ δ , t [ δ ] >
            
    cong-sub : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Sub Δ Γ}
               → t ≈ t'
               → γ ≋ γ'
               →  t [ γ ] ≈ t' [ γ' ]
               
    cong-<,> : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Sub Γ Δ}
               → t ≈ t'
               → γ ≋ γ'
               → < γ , t > ≋ < γ' , t' >
               
    cong-∘ : ∀ {Γ Δ Θ} {γ δ : Sub Δ Θ} {γ' δ' : Sub Γ Δ}
             → γ ≋ δ
             → γ' ≋ δ'
             → γ ∘ γ' ≋ δ ∘ δ'

  setoidT : ∀ {Γ α} → Setoid _ _
  setoidT {Γ} {α} = record { isEquivalence = IsEquivT {Γ} {α} }

  setoidS : ∀ {Γ Δ} → Setoid _ _
  setoidS {Γ} {Δ} = record { isEquivalence = IsEquivS {Δ} {Γ} }

  ⇑ : ∀ {Γ Δ α} (γ : Sub Δ Γ) → Sub (Δ ∙ α) (Γ ∙ α)
  ⇑ γ = < γ ∘ p , q >

  weaken : ∀ {Γ α} → Tm Γ α → Tm (Γ ∙ α) α
  weaken = _[ p ]

record Lambda-scwf : Set₁ where
  field
    scwf : Scwf
    
  open Scwf scwf public

  field

    -- Function type
    
    _`→_ : Ty → Ty → Ty

    -- lambda terms and apply
    
    lam : ∀ {Γ α β} → Tm (Γ ∙ α) β → Tm Γ (α `→ β)
    app : ∀ {Γ α β} → Tm Γ (α `→ β) → Tm Γ α → Tm Γ β

    -- substituting under apply and lambda
    
    subApp : ∀ {Γ Δ α β} (t : Tm Γ (α `→ β)) (u : Tm Γ α) (γ : Sub Δ Γ)
             → app (t [ γ ]) (u [ γ ]) ≈ (app t u) [ γ ] 
             
    subLam : ∀ {Γ Δ α β} (t : Tm (Γ ∙ α) β) (γ : Sub Δ Γ)
             → lam t [ γ ] ≈ lam (t [ < γ ∘ p , q > ])

    -- congruence rules
    
    cong-lam : ∀ {Γ α β} {t t' : Tm (Γ ∙ α) β}
               → t ≈ t'
               → lam t ≈ lam t'
             
    cong-app : ∀ {Γ α β} {t t' : Tm Γ (α `→ β)} {u u'}
               → t ≈ t'
               → u ≈ u'
               → app t u ≈ app t' u'

record Lambda-βη-scwf : Set₁ where
  field
    lambda-scwf : Lambda-scwf
  open Lambda-scwf lambda-scwf public

  field

   -- beta and eta equalities
  
    β : ∀ {Γ α β} {t : Tm (Γ ∙ α) β} {u}
        → app (lam t) u ≈ t [ < id , u > ]
        
    η : ∀ {Γ α β} {t : Tm Γ (α `→ β)}
        → lam (app (t [ p ]) q) ≈ t


{-
record Scwf-Morphism : Set₁ where
  field
    src : Scwf
    trg : Scwf
  open Scwf src
    renaming (Ctx to CtxS ; ⋄ to ⋄S ; Ty to TyS ; Tm to TmS
             ; Sub to SubS ; <> to <>S ; <_,_> to <_,_>S ; _∘_ to _∘S_
             ; _[_] to _[_]S ; q to qS ; p to pS ; id to idS ; _≈_ to _≈S_ ; _≋_ to _≋S_)
  open Scwf trg
    renaming (Ctx to CtxT ; ⋄ to ⋄T ; Ty to TyT ; Tm to TmT
             ; Sub to SubT ; <> to <>T ; <_,_> to <_,_>T ;_∘_ to _∘T_
             ; _[_] to _[_]T ; q to qT ; p to pT ; id to idT ; _≈_ to _≈T_ ; _≋_ to _≋T_)
  field
    to-ctx : CtxS → CtxT
    to-ty  : TyS → TyT
    ⟦_⟧  : ∀ {Γ α} → TmS Γ α → TmT (to-ctx Γ) (to-ty α)
    ⟦_⟧' : ∀ {Δ Γ} → SubS Γ Δ → SubT (to-ctx Γ) (to-ctx Δ)

--     ⋄-preserved : ∀ {Γ α} → to-ctx (Γ ∙ α) 

    id-preserved : ∀ {Γ} → ⟦ idS {Γ} ⟧' ≋T idT
    
    q-preserved : ∀ {Γ α} → ⟦ qS {Γ} {α}  ⟧ ≈T {!qT!}
    
    p-preserved : ∀ {Γ α} → ⟦ pS {Γ} {α} ⟧' ≋T {!!}
    
    ∘-preserved : ∀ {Δ Γ Θ} (σ₁ : SubS Θ Γ) (σ₂ : SubS Δ Θ)
                  → ⟦ σ₁ ∘S σ₂ ⟧' ≋T ⟦ σ₁ ⟧' ∘T ⟦ σ₂ ⟧'

    <>-preserved : ∀ {Γ} → ⟦ <>S {Γ} ⟧' ≋T {!<>T!}

    <,>-preserved : ∀ {Γ Δ α} (t : TmS Γ α) (σ : SubS Γ Δ)
                    → ⟦ < σ , t >S ⟧' ≋T {!!} --< ⟦ σ ⟧' , ⟦ t ⟧ >T

    sub-preserved : ∀ {Γ Δ α} (t : TmS Γ α) (σ : SubS Δ Γ)
                    → ⟦ t [ σ ]S ⟧ ≈T ⟦ t ⟧ [ ⟦ σ ⟧' ]T
-}
