---------------------------------------------------------------------
-- A relation for β conversion for the lambda calculus and
-- setoid definition. The isomorphism between cwf terms and
-- untyped lambda calculus terms is on this setoid.
---------------------------------------------------------------------

module Unityped.ImpSub.Beta where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_])
open import Function as F using (_$_ ; flip)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Unityped.ImpSub.Syntax
open import Unityped.ImpSub.Substitution
open import Unityped.ImpSub.Properties
open import Unityped.ImpSub.UcwfImpSub
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_])

---------------------------------------------------------------------
-- β convertability as an inductive relation over terms

infix 5 _~βη_
infix 5 _≈βη_

data _~βη_  {n} : (_ _ : Tm n) → Set where

  varcong : (i : Fin n) → var i ~βη var i
  
  apcong : ∀ {t u t′ u′}
           → t ~βη t′
           → u ~βη u′
           → t · u ~βη t′ · u′
               
  ξ : {t u : Tm (1 + n)}
      → t ~βη u
      → ƛ t ~βη ƛ u
               
  β : ∀ (t : Tm (1 + n)) u → ƛ t · u ~βη t [ id , u ]
               
  η : ∀ t → ƛ (weaken t · q) ~βη t
  
  sym~βη : ∀ {t₁ t₂}
           → t₁ ~βη t₂
           → t₂ ~βη t₁
               
  trans~βη : ∀ {t₁ t₂ t₃}
             → t₁ ~βη t₂
             → t₂ ~βη t₃
             → t₁ ~βη t₃

data _≈βη_ {m} : ∀ {n} (_ _ : Subst m n) → Set where

  ⋄ : ∀ {ρ ρ' : Subst m 0} → ρ ≈βη ρ'

  ext : ∀ {n} {t u} {ρ ρ' : Subst m n}
        → t ~βη u
        → ρ ≈βη ρ'
        → (ρ , t) ≈βη (ρ' , u)

-- Reflexivity and setoid instances for above relations

refl~βη : ∀ {n} {t : Tm n} → t ~βη t
refl~βη = trans~βη (sym~βη (η _)) (η _)

refl≈βη : ∀ {m n} {ρ : Subst m n} → ρ ≈βη ρ
refl≈βη {ρ = []}    = ⋄
refl≈βη {ρ = _ ∷ _} = ext refl~βη refl≈βη

sym≈βη : ∀ {m n} {ρ ρ' : Subst m n} → ρ ≈βη ρ' → ρ' ≈βη ρ
sym≈βη ⋄ = ⋄
sym≈βη (ext x ρ~ρ') = ext (sym~βη x) (sym≈βη ρ~ρ')

trans≈βη : ∀ {m n} {ρ₁ ρ₂ ρ₃ : Subst m n} → ρ₁ ≈βη ρ₂ → ρ₂ ≈βη ρ₃ → ρ₁ ≈βη ρ₃
trans≈βη ⋄ _ = ⋄
trans≈βη (ext x ρ₁≈ρ₂) (ext y ρ₂≈ρ₃) = ext (trans~βη x y) (trans≈βη ρ₁≈ρ₂ ρ₂≈ρ₃)

~βηequiv : ∀ {n} → IsEquivalence (_~βη_ {n})
~βηequiv = record { refl  = refl~βη
                  ; sym   = sym~βη
                  ; trans = trans~βη
                  }

-- Instance of setoid for Tm under _~βη_

TmSetoid : ∀ {n} → Setoid _ _ 
TmSetoid {n} = record { Carrier = Tm n
                      ; _≈_ = _~βη_
                      ; isEquivalence = ~βηequiv
                      }

-- Transforms a proof of two terms in identity to the beta eta equality

≡-to~βη : ∀ {n} {t u : Tm n} → t ≡ u → t ~βη u
≡-to~βη refl = refl~βη

-- Transforms a proof of two substitutions in identity to the beta eta equality

≡-to-≈βη : ∀ {m n} {ρ σ : Subst m n} → ρ ≡ σ → ρ ≈βη σ
≡-to-≈βη refl = refl≈βη

-----------------------------------------------------------------------------------------
-- Congruence rule proofs

cong-ext : ∀ {m n} {t t' : Tm n} {ρ ρ' : Subst n m}
           → t ~βη t'
           → ρ ≈βη ρ'
           → (ρ , t) ≈βη (ρ' , t')
cong-ext t~t' ⋄            = ext t~t' ⋄
cong-ext t~t' (ext x ρ≈ρ') = ext t~t' (cong-ext x ρ≈ρ')         

lookup-sub : ∀ {m n} {ρ ρ' : Subst m n} (i : Fin n)
             → ρ ≈βη ρ'
             → lookup i ρ ~βη lookup i ρ'
lookup-sub ()      ⋄
lookup-sub zero    (ext t~u _)    = t~u
lookup-sub (suc i) (ext _   ρ≈ρ') = lookup-sub i ρ≈ρ'

η-help : ∀ {n m} (t : Tm n) (ρ : Subst m n)
         → weaken (t [ ρ ]) ≡ (weaken t) [ ↑ ρ ]
η-help t ρ = sym $ begin
  weaken t [ ↑ ρ ]                ≡⟨⟩
  weaken t [ weaken-subst ρ , q ] ≡⟨ cong (λ x → weaken t [ x , q ]) (sym (mapWk-∘p ρ)) ⟩
  weaken t [ ρ ∘ p , q ]          ≡⟨ cong (_[ ρ ∘ p , q ]) (wk-[p] t) ⟩
  t [ p ] [ ρ ∘ p , q ]           ≡⟨ sym (subComp t p (ρ ∘ p , q)) ⟩
  t [ p ∘ (ρ ∘ p , q) ]           ≡⟨ cong (t [_]) (pCons (ρ ∘ p) q) ⟩
  t [ ρ ∘ p ]                     ≡⟨ subComp t ρ p ⟩
  (t [ ρ ]) [ p ]                 ≡⟨ sym (wk-[p] (t [ ρ ])) ⟩
  weaken (t [ ρ ])                ∎ where open P.≡-Reasoning

β-help : ∀ {m n} (t : Tm (suc n)) u (ρ : Subst m n)
         → t [ ↑ ρ ] [ id , u [ ρ ] ] ≡ t [ id , u ] [ ρ ]
β-help t u ρ = begin
  t [ ↑ ρ ] [ id , u [ ρ ] ]                          ≡⟨ sym (subComp t (↑ ρ) (id , u [ ρ ])) ⟩
  t [ ↑ ρ ∘ (id , u [ ρ ]) ]                          ≡⟨⟩
  t [ (weaken-subst ρ , q) ∘ (id , u [ ρ ]) ]         ≡⟨ cong (λ x → t [ (x , q) ∘ (id , u [ ρ ]) ]) (sym (mapWk-∘p _)) ⟩
  t [ (ρ ∘ p , q) ∘ (id , u [ ρ ]) ]                  ≡⟨⟩
  t [ (ρ ∘ p) ∘ (id , u [ ρ ]) , u [ ρ ] ]            ≡⟨ cong (λ x → t [ x , u [ ρ ] ]) (assoc ρ p _) ⟩
  t [ ρ ∘ (p ∘ (id , u [ ρ ])) , u [ ρ ] ]            ≡⟨ cong (λ x → t [ ρ ∘ x , u [ ρ ] ]) (pCons _ _) ⟩
  t [ ρ ∘ id , u [ ρ ] ]                              ≡⟨ cong (λ x → t [ x , u [ ρ ] ]) (idR ρ) ⟩
  t [ ρ , u [ ρ ] ]                                   ≡⟨ cong (λ x → t [ x , u [ ρ ] ]) (sym (idL ρ)) ⟩
  t [ id ∘ ρ , u [ ρ ] ]                              ≡⟨⟩
  t [ (id , u) ∘ ρ ]                                  ≡⟨ subComp t (id , u) ρ ⟩
  t [ id , u ] [ ρ ]                                  ∎ where open P.≡-Reasoning

congSub-t : ∀ {m n} {t t' : Tm n} {ρ : Subst m n}
            → t ~βη t'
            → t [ ρ ] ~βη t' [ ρ ]
congSub-t (varcong i)         = refl~βη
congSub-t (apcong t~t' t~t'') = apcong (congSub-t t~t') (congSub-t t~t'')
congSub-t (ξ t~t')            = ξ (congSub-t t~t')
congSub-t {ρ = ρ} (β t u)
  rewrite sym $ β-help t u ρ = β (t [ ↑ ρ ]) (u [ ρ ])
congSub-t {ρ = ρ} (η a) rewrite cong (ƛ F.∘ (_· q)) (sym (η-help a ρ)) = η (a [ ρ ])
congSub-t (sym~βη t~t')         = sym~βη (congSub-t t~t')
congSub-t (trans~βη t~t' t~t'') = trans~βη (congSub-t t~t') (congSub-t t~t'')

cong-∘≈₁ : ∀ {m n k} {σ σ' : Subst m n} {γ : Subst k m}
           → σ ≈βη σ'
           → σ ∘ γ ≈βη σ' ∘ γ
cong-∘≈₁ {σ = []} {[]} ⋄ = refl≈βη
cong-∘≈₁ {γ = γ} (ext t~u σ≈σ') = cong-ext (congSub-t {ρ = γ} t~u) (cong-∘≈₁ σ≈σ')

↑ρ-pr : ∀ {m n} {γ δ : Subst m n}
        → γ ≈βη δ
        → ↑ γ ≈βη ↑ δ
↑ρ-pr {γ = γ} {δ} γ≈δ
  rewrite  sym (mapWk-∘p γ)
         | sym (mapWk-∘p δ) = cong-ext refl~βη (cong-∘≈₁ γ≈δ)

congSub-s : ∀ {m n} {t : Tm n} {ρ ρ' : Subst m n}
            → ρ ≈βη ρ'
            → t [ ρ ] ~βη t [ ρ' ]
congSub-s {ρ = []} {[]}     ⋄            = refl~βη
congSub-s {t = var zero}    (ext x ρ≈ρ') = x
congSub-s {t = var (suc i)} (ext x ρ≈ρ') = congSub-s {t = var i} ρ≈ρ'
congSub-s {t = a · b}       (ext x ρ≈ρ') = apcong (congSub-s {t = a} (ext x ρ≈ρ')) (congSub-s {t = b} (ext x ρ≈ρ'))
congSub-s {t = ƛ b}         (ext x ρ≈ρ') = ξ (congSub-s {t = b} (↑ρ-pr (ext x ρ≈ρ')))

cong-[] : ∀ {m n} {t t' : Tm n} {ρ ρ' : Subst m n}
          → t ~βη t'
          → ρ ≈βη ρ'
          → t [ ρ ] ~βη t' [ ρ' ]
cong-[] {t' = t'} t~t' ρ≈ρ' = trans~βη (congSub-t t~t') (congSub-s {t = t'} ρ≈ρ')

cong-∘≈ : ∀ {m n k} {ρ σ : Subst m n} {ρ' σ' : Subst k m}
          → ρ ≈βη σ
          → ρ' ≈βη σ'
          → ρ ∘ ρ' ≈βη σ ∘ σ'
cong-∘≈ ⋄           ρ'~σ'         = ⋄
cong-∘≈ (ext t ρ≈σ) ⋄             = ext (cong-[] t ⋄) (cong-∘≈ ρ≈σ ⋄)
cong-∘≈ (ext t ρ≈σ) (ext u ρ'≈σ') = ext (cong-[] t (ext u ρ'≈σ')) (cong-∘≈ ρ≈σ (ext u ρ'≈σ'))
