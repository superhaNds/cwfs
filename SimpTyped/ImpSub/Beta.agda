module SimpTyped.ImpSub.Beta where

open import SimpTyped.ImpSub.Syntax
open import SimpTyped.Type
open import SimpTyped.Context
open import SimpTyped.ImpSub.Properties
open import SimpTyped.ImpSub.Tm-Scwf
open import Data.Product
open import Data.Unit
open import Function as F using (_$_)
open import Relation.Binary using (IsEquivalence ; Setoid)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_])

infix 5 _~βη_
infix 5 _≈βη_

data _~βη_ {Γ} : ∀ {α} (_ _ : Tm Γ α) → Set where

  varcong : ∀ {α} (v : α ∈ Γ) → var v ~βη var v
       
  apcong : ∀ {α β} {t t' : Tm Γ (α ⇒ β)} {u u'}
           → t ~βη t'
           → u ~βη u'
           → (t · u) ~βη (t' · u')
           
  ξ : ∀ {α β} {t t' : Tm (Γ ∙ α) β}
      → t ~βη t'
      → ƛ t ~βη ƛ t'
  
  β : ∀ {α β} (t : Tm (Γ ∙ α) β) u → ƛ t · u ~βη (t [ id , u ])

  η : ∀ {α β} (t : Tm Γ (α ⇒ β)) → ƛ (t [ p ] · q) ~βη t
       
  sym~βη : ∀ {α} {t₁ t₂ : Tm Γ α}
           → t₁ ~βη t₂
           → t₂ ~βη t₁
              
  trans~βη : ∀ {α} {t₁ t₂ t₃ : Tm Γ α}
             → t₁ ~βη t₂
             → t₂ ~βη t₃
             → t₁ ~βη t₃
  
data _≈βη_ {Δ} : ∀ {Γ} (_ _ : Sub Δ Γ) → Set where

  ⋄ : {γ γ' : Sub Δ ε} → γ ≈βη γ'
  
  ext : ∀ {Γ α} {t u : Tm Δ α}
          {γ γ' : Sub Δ Γ}
        → t ~βη u
        → γ ≈βη γ'
        → (γ , t) ≈βη (γ' , u)

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

cong-ext : ∀ {Γ Δ α} {t t' : Tm Γ α} {ρ ρ' : Sub Γ Δ}
           → t ~βη t'
           → ρ ≈βη ρ'
           → (ρ , t) ≈βη (ρ' , t')
cong-ext t~t' ⋄            = ext t~t' ⋄
cong-ext t~t' (ext x ρ≈ρ') = ext t~t' (cong-ext x ρ≈ρ')

β-help : ∀ {Γ Δ α β} (t : Tm (Γ ∙ α) β) u (γ : Sub Δ Γ)
         → t [ wk-sub _ ⊆-∙ γ , q ] [ id , u [ γ ] ] ≡ t [ id , u ] [ γ ]
β-help t u γ = begin
  t [ wk-sub _ ⊆-∙ γ , q ] [ id , u [ γ ] ]
    ≡⟨ cong (λ x → t [ x , q ] [ id , u [ γ ] ]) (sym (wk-sub-∘-p γ)) ⟩
  t [ γ ∘ p , q ] [ id , u [ γ ] ]
    ≡⟨ sym $ subComp t (γ ∘ p , q) (id , (u [ γ ])) ⟩
  t [ (γ ∘ p , q) ∘ (id , u [ γ ]) ]
    ≡⟨⟩
  t [ (γ ∘ p) ∘ (id , u [ γ ]) , u [ γ ] ]
    ≡⟨ cong (λ x → t [ x , u [ γ ] ]) (assoc γ _ _) ⟩
  t [ γ ∘ (p ∘ (id , u [ γ ])) , u [ γ ] ]
    ≡⟨ cong (λ x → t [ γ ∘ x , u [ γ ] ]) (pCons (u [ γ ]) id) ⟩
  t [ γ ∘ id , u [ γ ] ]
    ≡⟨ cong (λ x → t [ x , u [ γ ] ]) (idR γ) ⟩
  t [ γ , u [ γ ] ]
    ≡⟨ cong (λ x → t [ x , u [ γ ] ]) (sym (idL γ)) ⟩
  t [ id ∘ γ , u [ γ ] ]
    ≡⟨⟩
  t [ (id , u ) ∘ γ ]
    ≡⟨ subComp t (id , u) γ ⟩
  t [ id , u ] [ γ ]
    ∎ where open P.≡-Reasoning
  
η-help : ∀ {Γ Δ α β} (t : Tm Γ (α ⇒ β)) (γ : Sub Δ Γ)
         → (t [ γ ]) [ p {α = α} ] ≡ t [ p ] [ wk-sub Γ ⊆-∙ γ , q ] 
η-help t γ = sym $ begin
  t [ p ] [ wk-sub _ ⊆-∙ γ , q ]
    ≡⟨ cong (λ x → t [ p ] [ x , q ]) (sym (wk-sub-∘-p γ)) ⟩
  t [ p ] [ γ ∘ p , q ]
    ≡⟨ sym (subComp t _ (γ ∘ p , q)) ⟩
  t [ p ∘ (γ ∘ p , q ) ]
    ≡⟨ cong (t [_]) (pCons q (γ ∘ p)) ⟩
  t [ γ ∘ p ]
    ≡⟨ subComp t γ p ⟩
  t [ γ ] [ p ]
    ∎ where open P.≡-Reasoning

congSub-t : ∀ {Γ Δ α} {t t' : Tm Γ α} {ρ : Sub Δ Γ} → t ~βη t' → t [ ρ ] ~βη t' [ ρ ]
congSub-t (varcong v) = refl~βη
congSub-t (apcong t~t' t~t'') = apcong (congSub-t t~t') (congSub-t t~t'')
congSub-t (ξ t~t') = ξ (congSub-t t~t')
congSub-t {ρ = ρ} (β t u)
  rewrite sym $ β-help t u ρ = β (t [ wk-sub _ ⊆-∙ ρ , q ]) (u [ ρ ])
congSub-t {Γ} {Δ} {α = F ⇒ G} {ρ = ρ} (η a)
  rewrite cong (λ x → ƛ (x · q)) (sym $ η-help a ρ)= η (a [ ρ ])
congSub-t (sym~βη t~t') = sym~βη (congSub-t t~t')
congSub-t (trans~βη t~t' t~t'') = trans~βη (congSub-t t~t') (congSub-t t~t'')

cong-∘≈₁ : ∀ {Γ Δ Ξ} {σ σ' : Sub Δ Γ} {γ : Sub Ξ Δ} → σ ≈βη σ' → σ ∘ γ ≈βη σ' ∘ γ
cong-∘≈₁ {σ = tt} {tt} ⋄ = refl≈βη
cong-∘≈₁ {γ = γ} (ext x σ≈σ') = cong-ext (congSub-t {ρ = γ} x) (cong-∘≈₁ σ≈σ')

↑-preserv : ∀ {Γ Δ α} {γ δ : Sub Γ Δ} → γ ≈βη δ
            → (wk-sub _ (⊆-∙ {a = α}) γ , q) ≈βη (wk-sub _ ⊆-∙ δ , q)
↑-preserv {α = α} {γ = γ} {δ} γ≈δ
  rewrite sym $ (wk-sub-∘-p {α = α} γ)
        | sym $ (wk-sub-∘-p {α = α} δ) = cong-ext refl~βη (cong-∘≈₁ γ≈δ)

congSub-s : ∀ {Γ Δ α} {t : Tm Δ α} {ρ ρ' : Sub Γ Δ} → ρ ≈βη ρ' → t [ ρ ] ~βη t [ ρ' ]
congSub-s {ρ = tt}            ⋄            = refl~βη
congSub-s {t = var here}      (ext x ρ≈ρ') = x
congSub-s {t = var (there v)} (ext x ρ≈ρ') =
  congSub-s {t = var v} ρ≈ρ'
congSub-s {t = a · b}         (ext x ρ≈ρ') =
  apcong (congSub-s {t = a} (ext x ρ≈ρ')) (congSub-s {t = b} (ext x ρ≈ρ'))
congSub-s {t = ƛ b}           (ext x ρ≈ρ') =
  ξ (congSub-s {t = b} (↑-preserv (ext x ρ≈ρ')))
