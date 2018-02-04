module SimpTyped.Tm.Beta where

open import SimpTyped.Tm.Syntax
open import SimpTyped.Type
open import SimpTyped.Context
open import Data.Product
open import Relation.Binary using (IsEquivalence ; Setoid)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_])

infix 5 _~βη_
infix 5 _≈βη_

data _~βη_ {Γ} : ∀ {α} (_ _ : Tm Γ α) → Set where

  varcong : ∀ {α} (v : α ∈ Γ) → var v ~βη var v
       
  apcong : ∀ {α β} {t t' : Tm Γ (α ⇒ β)} {u u'} →
            t ~βη t' →
            u ~βη u' →
            (t · u) ~βη (t' · u)
           
  ξ : ∀ {α β} {t t' : Tm (Γ ∙ α) β} →
       t ~βη t' → ƛ t ~βη ƛ t'
  
  β : ∀ {α β} (t : Tm (Γ ∙ α) β) u →
       ƛ t · u ~βη (t [ id , u ])

  η : ∀ {α β} (t : Tm Γ (α ⇒ β)) → ƛ (t [ p ] · q) ~βη t
       
  sym~βη : ∀ {α} {t₁ t₂ : Tm Γ α} →
            t₁ ~βη t₂ →
            t₂ ~βη t₁
              
  trans~βη : ∀ {α} {t₁ t₂ t₃ : Tm Γ α} →
              t₁ ~βη t₂ →
              t₂ ~βη t₃ →
              t₁ ~βη t₃
  
data _≈βη_ {Δ} : ∀ {Γ} (_ _ : Sub Δ Γ) → Set where

  ⋄ : {γ γ' : Sub Δ ε} → γ ≈βη γ'
  
  ext : ∀ {Γ α}
          {t u : Tm Δ α}
          {γ γ' : Sub Δ Γ} →          
         t ~βη u → γ ≈βη γ' → (γ , t) ≈βη (γ' , u)

refl~βη : ∀ {Γ α} {t : Tm Γ α} → t ~βη t
refl~βη {t = t} = trans~βη (sym~βη (β (var here) t)) (β (var here) t)

refl≈βη : ∀ {Γ Δ} {ρ : Sub Γ Δ} → ρ ≈βη ρ
refl≈βη {Δ = ε} = ⋄
refl≈βη {Δ = Δ ∙ x} = ext refl~βη refl≈βη

sym≈βη : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → σ ≈βη σ' → σ' ≈βη σ
sym≈βη ⋄ = ⋄
sym≈βη (ext x σ≈σ') = ext (sym~βη x) (sym≈βη σ≈σ')

trans≈βη : ∀ {Γ Δ} {ρ₁ ρ₂ ρ₃ : Sub Γ Δ} → ρ₁ ≈βη ρ₂ → ρ₂ ≈βη ρ₃ → ρ₁ ≈βη ρ₃
trans≈βη ⋄ _ = ⋄
trans≈βη (ext x ρ₁≈ρ₂) (ext y ρ₂≈ρ₃) = ext (trans~βη x y) (trans≈βη ρ₁≈ρ₂ ρ₂≈ρ₃)

~βηequiv : ∀ {Γ α} → IsEquivalence (_~βη_ {Γ} {α})
~βηequiv = record { refl  = refl~βη
                  ; sym   = sym~βη
                  ; trans = trans~βη
                  }

-- Instance of setoid for Tm under _~βη_

TmSetoid : ∀ {Γ α} → Setoid _ _ 
TmSetoid {Γ} {α} =
  record { Carrier = Tm Γ α
         ; _≈_ = _~βη_
         ; isEquivalence = ~βηequiv
         }

-- Transforms a proof of two terms in identity to the beta eta equality

≡-to~βη : ∀ {Γ α} {t u : Tm Γ α} → t ≡ u → t ~βη u
≡-to~βη refl = refl~βη

-- Transforms a proof of two substitutions in identity to the beta eta equality

≡-to-≈βη : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → ρ ≡ σ → ρ ≈βη σ
≡-to-≈βη refl = refl≈βη
