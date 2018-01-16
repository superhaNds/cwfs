module Ext-Typed.DTyped.Cwf where


open import Agda.Primitive
open import Relation.Binary

record Cwf : Set₁ where

  infix 4 _≊_
  infix 4 _≈_
  field
    Ctx : Set
    Sub : Ctx → Ctx → Set
    Ty  : Ctx → Set
    _⊢_ : (Γ : Ctx) → Ty Γ → Set

    ⋄   : Ctx
    _,_ : (Γ : Ctx) → Ty Γ → Ctx

    _≈_ : ∀ {Γ} {A : Ty Γ} → Rel (Γ ⊢ A) lzero
    _≊_ : ∀ {Δ Γ} → Rel (Sub Δ Γ) lzero
    
    _[_]T : ∀ {Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ   
    _[_]  : ∀ {Δ Γ} {A : Ty Γ} (t : Γ ⊢ A) (γ : Sub Δ Γ) → Δ ⊢ (A [ γ ]T)

    id  : ∀ {Γ} → Sub Γ Γ
    _∘_ : ∀ {Θ Δ Γ} → Sub Γ Θ → Sub Δ Γ → Sub Δ Θ

    <> : ∀ {Γ} → Sub Γ ⋄

    <_,_> : ∀ {Δ Γ} (A : Ty Γ) (γ : Sub Δ Γ)
              (t : Δ ⊢ (A [ γ ]T)) → Sub Δ (Γ , A)
    p : ∀ {Γ} {A : Ty Γ} → Sub (Γ , A) Γ
    q : ∀ {Γ} (A : Ty Γ) → (Γ , A) ⊢ (A [ p ]T)

    id₀   : id {⋄} ≊ <>
    
    <>-∘   : ∀ {Γ Δ} (γ : Sub Γ Δ) →
             <> ∘ γ ≊ <>
    
   -- varp  : ∀ {Γ} {A : Ty Γ} → id {Γ , A} ≊ < p , q >
    
    idL   : ∀ {Γ Δ} (γ : Sub Δ Γ) → id ∘ γ ≊ γ
    
    idR   : ∀ {Γ Δ} (γ : Sub Γ Δ) → γ ∘ id ≊ γ
    
    assoc : ∀ {Γ Δ Θ Λ} (γ : Sub Δ Θ) (δ : Sub Γ Δ) (ζ : Sub Λ Γ) →
             (γ ∘ δ) ∘ ζ ≊ γ ∘ (δ ∘ ζ)

--    tyId : ∀ {Γ} (A : Ty Γ) → t [ id ]T ≈ 
  {-          
    tmId  : ∀ {Γ} {A : Ty Γ} (t : Γ ⊢ A) → t [ id ] ≈ ?
    
    pCons : ∀ {Δ Θ} {A : Ty Δ} (t : Δ ⊢ A) (γ : Sub Δ Θ) → p ∘ < γ , t > ≊ γ
    
    q[]   : ∀ {Γ Δ} {A : Ty Γ} (t : Γ ⊢ A) (γ : Sub Γ Δ) → q [ < γ , t > ] ≈ t
    
    clos  : ∀ {Γ Δ Θ α} (t : Δ ⊢ α) (γ : Sub Γ Δ) (δ : Sub Θ Γ) →
             t [ γ ∘ δ ] ≈ t [ γ ] [ δ ]
            
    maps  : ∀ {Γ Δ α} (t : Δ ⊢ α) (γ : Sub Δ Γ) (δ : Sub Γ Δ) →
             < γ , t > ∘ δ ≊ < γ ∘ δ , t [ δ ] >
            
    cong-[] : ∀ {Γ Δ α} {t t' : Γ ⊢ α} {γ γ' : Sub Δ Γ} →
               t ≈ t' →
               γ ≊ γ' →
               t [ γ ] ≈ t' [ γ' ]
               
    cong-<,> : ∀ {Γ Δ α} {t t' : Γ ⊢ α} {γ γ' : Sub Γ Δ} →
                t ≈ t' →
                γ ≊ γ' →
                < γ , t > ≊ < γ' , t' >
               
    cong-∘ : ∀ {Γ Δ Θ} {γ δ : Sub Δ Θ} {γ' δ' : Sub Γ Δ} →
              γ ≊ δ →
              γ' ≊ δ' →
              γ ∘ γ' ≊ δ ∘ δ'
-}


