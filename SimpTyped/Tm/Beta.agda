module SimpTyped.Tm.Beta where

open import SimpTyped.Tm.Syntax
open import SimpTyped.Type
open import SimpTyped.Context
open import Data.Product

infix 7 _~βη_
infix 7 _≈βη_

data _~βη_ {Γ} : ∀ {α} (_ _ : Tm Γ α) → Set where

  varcong : ∀ {α} (v : α ∈ Γ) → var v ~βη var v
       
  apcong : ∀ {α β} {t t' : Tm Γ (α ⇒ β)}
             {u u' : Tm Γ α} →
            t ~βη t' →
            u ~βη u' →
            (t · u) ~βη (t' · u)
           
  ξ : ∀ {α β}
        {t t' : Tm (Γ ∙ α) β} →
       t ~βη t' →
       ƛ t ~βη ƛ t'
  
  β : ∀ {α β}
        (t : Tm (Γ ∙ α) β)
        (u : Tm Γ α) →
       ƛ t · u ~βη (t [ id , u ])
       
  sym~βη    : ∀ {α} {t₁ t₂ : Tm Γ α} →
              t₁ ~βη t₂ →
              t₂ ~βη t₁
              
  trans~βη  : ∀ {α} {t₁ t₂ t₃ : Tm Γ α} →
               t₁ ~βη t₂ →
               t₂ ~βη t₃ →
               t₁ ~βη t₃
  
data _≈βη_ {Δ} : ∀ {Γ} (_ _ : Sub Δ Γ) → Set where

  ⋄ : {γ γ' : Sub Δ ε} → γ ≈βη γ'
  
  ext : ∀ {Γ α}
          {t u : Tm Δ α}
          {γ γ' : Sub Δ Γ} →          
         t ~βη u → γ ≈βη γ' → (γ , t) ≈βη (γ' , u)
