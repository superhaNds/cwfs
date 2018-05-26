module SimpTyped.ExpSub where

open import SimpTyped.Context
open import SimpTyped.Type

data Tm : Ctx → Ty → Set

data Sub : Ctx → Ctx → Set

data Tm where
  q    : ∀ {Γ α}                      → Tm (Γ ∙ α) α
  _[_] : ∀ {Γ Δ α} → Tm Γ α → Sub Δ Γ → Tm Δ α

data Sub where
  id    : ∀ {Γ}                         → Sub Γ Γ
  _∘_   : ∀ {Γ Δ Θ} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  p     : ∀ {Γ α}                       → Sub (Γ ∙ α) Γ
  <>    : ∀ {Δ}                         → Sub Δ ε
  <_,_> : ∀ {Γ Δ α} → Sub Δ Γ → Tm Δ α  → Sub Δ (Γ ∙ α)

infix 4 _~_
infix 4 _≈_

data _~_ : ∀ {Γ α} → Tm Γ α → Tm Γ α → Set

data _≈_ : ∀ {Γ Δ} → Sub Δ Γ → Sub Δ Γ → Set

data _~_ where
  qSub : ∀ {Γ Δ α} {γ : Sub Δ Γ} {t : Tm Δ α} → q [ < γ , t > ] ~ t

  subId : ∀ {Γ α} {t : Tm Γ α} → t [ id ] ~ t

  subComp : ∀ {Γ Δ Θ α} {t : Tm Θ α} {γ : Sub Δ Θ} {δ : Sub Γ Δ}
            → t [ γ ∘ δ ] ~ t [ γ ] [ δ ]

  cong-sub : ∀ {Γ Δ α} {γ γ' : Sub Δ Γ} {t t' : Tm Γ α}
             → t ~ t'
             → γ ≈ γ'
             → t [ γ ] ~ t' [ γ' ]

  sym~ : ∀ {Γ α} {t₁ t₂ : Tm Γ α}
         → t₁ ~ t₂
         → t₂ ~ t₁

  trans~ : ∀ {Γ α} {t₁ t₂ t₃ : Tm Γ α}
           → t₁ ~ t₂
           → t₂ ~ t₃
           → t₃ ~ t₁

refl~ : ∀ {Γ α} {t : Tm Γ α} → t ~ t
refl~ = trans~ (sym~ subId) subId

data _≈_ where
  left-zero : ∀ {Γ Δ} {γ : Sub Δ Γ} → <> ∘ γ ≈ <>
  
  id-zero : id {ε} ≈ <>

  idL : ∀ {Γ Δ} {γ : Sub Δ Γ} → id ∘ γ ≈ γ

  idR : ∀ {Γ Δ} {γ : Sub Δ Γ} → γ ∘ id ≈ γ

  ∘-asso : ∀ {Γ Δ Θ Ξ} {γ₁ : Sub Δ Θ } {γ₂ : Sub Γ Δ} {γ₃ : Sub Ξ Γ}
           → (γ₁ ∘ γ₂) ∘ γ₃ ≈ γ₁ ∘ (γ₂ ∘ γ₃)

  p-∘ : ∀ {Γ Δ α} {γ : Sub Δ Γ} {t : Tm Δ α} → p ∘ < γ , t > ≈ γ

  idExt : ∀ {Γ α} → id {Γ ∙ α} ≈ < p , q >

  compExt : ∀ {Γ Δ Θ α} {γ : Sub Δ Θ} {δ : Sub Γ Δ} {t : Tm Δ α}
            → < γ , t > ∘ δ ≈ < γ ∘ δ , t [ δ ] >

  cong-<,> : ∀ {Γ Δ α} {γ γ' : Sub Δ Γ} {t t' : Tm Δ α}
             → t ~ t'
             → γ ≈ γ'
             → < γ , t > ≈ < γ' , t' >

  sym≈ : ∀ {Γ Δ} {γ₁ γ₂ : Sub Δ Γ}
         → γ₁ ≈ γ₂
         → γ₂ ≈ γ₁
         
  trans≈ : ∀ {Γ Δ} {γ₁ γ₂ γ₃ : Sub Δ Γ}
           → γ₁ ≈ γ₂
           → γ₂ ≈ γ₃
           → γ₁ ≈ γ₃

refl≈ : ∀ {Γ Δ} {γ : Sub Δ Γ} → γ ≈ γ
refl≈ = trans≈ (sym≈ idL) idL
         
