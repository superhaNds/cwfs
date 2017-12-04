module SimpTyped.Tm.Beta where

open import SimpTyped.Tm.Syntax
open import SimpTyped.Type
open import SimpTyped.Context
open import Data.Product

infix 7 _~βη_
infix 7 _~~βη_

data _~βη_ {Γ} : ∀ {α} (_ _ : Term Γ α) → Set where
  varcong : ∀ {α} (v : α ∈ Γ) → var v ~βη var v
  apcong : ∀ {α β} {t t' : Term Γ (α ⇒ β)} {u u' : Term Γ α} → t ~βη t' → u ~βη u' →
           (t · u) ~βη (t' · u)
  ξ : ∀ {α β} {t t' : Term (Γ ∙ α) β} → t ~βη t' → ƛ t ~βη ƛ t'
  β : ∀ {α β} (t : Term (Γ ∙ α) β) (u : Term Γ α) → ƛ t · u ~βη (t [ id , u ])
  sym~βη    : ∀ {α} {t₁ t₂ : Term Γ α} → t₁ ~βη t₂ → t₂ ~βη t₁
  trans~βη  : ∀ {α} {t₁ t₂ t₃ : Term Γ α} → t₁ ~βη t₂ → t₂ ~βη t₃ → t₁ ~βη t₃
  
data _~~βη_ {Δ} : ∀ {Γ} (_ _ : Δ ▹ Γ) → Set where
  ⋄ : {γ γ' : Δ ▹ ε} → γ ~~βη γ'
  ext : ∀ {Γ α} {t u : Term Δ α} {γ γ' : Δ ▹ Γ} →
        t ~βη u → γ ~~βη γ' → (γ , t) ~~βη (γ' , u)
