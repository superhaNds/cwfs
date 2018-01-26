---------------------------------------------------------------------
-- A relation for β conversion for the lambda calculus and
-- setoid definition. The isomorphism between cwf terms and
-- untyped lambda calculus terms is on this setoid.
---------------------------------------------------------------------

module Unityped.Wellscoped.Beta where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_])
open import Function as F using (_$_ ; flip)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Unityped.Wellscoped.Syntax
open import Unityped.Wellscoped.Substitution
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality hiding ([_])

---------------------------------------------------------------------
-- β convertability as an inductive relation over terms

infix 5 _~βη_
infix 5 _≈βη_

data _~βη_  {n} : (_ _ : Tm n) → Set where

  varcong : (i : Fin n) → var i ~βη var i
  
  apcong : {t u t′ u′ : Tm n} →
            t ~βη t′ →
            u ~βη u′ →
            t · u ~βη t′ · u′
               
  ξ : {t u : Tm (1 + n)} → t ~βη u → ƛ t ~βη ƛ u
               
  β : ∀ {t : Tm (1 + n)} {u} → ƛ t · u ~βη t [ id , u ]
               
  η : {t : Tm n} → ƛ (weaken t · q) ~βη t
  
  sym~βη : {t₁ t₂ : Tm n} →
            t₁ ~βη t₂ →
            t₂ ~βη t₁
               
  trans~βη : {t₁ t₂ t₃ : Tm n} →
              t₁ ~βη t₂ →
              t₂ ~βη t₃ →
              t₁ ~βη t₃

data _≈βη_ {m} : ∀ {n} (_ _ : Subst m n) → Set where

  ⋄   : ∀ {ρ ρ' : Subst m 0} → ρ ≈βη ρ'

  ext : ∀ {n} {t u : Tm m} {ρ ρ' : Subst m n} →
         t ~βη u →
         ρ ≈βη ρ' →
         (ρ , t) ≈βη (ρ' , u)

-- Reflexivity and setoid instances for above relations

refl~βη : ∀ {n} {t : Tm n} → t ~βη t
refl~βη = trans~βη (sym~βη η) η

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

cong-, : ∀ {m n} {t t' : Tm n} {ρ ρ' : Subst n m} →
          t ~βη t' →
          ρ ≈βη ρ' →
          (ρ , t) ≈βη (ρ' , t')
cong-, t~t' ⋄            = ext t~t' ⋄
cong-, t~t' (ext x ρ≈ρ') = ext t~t' (cong-, x ρ≈ρ')         

lookup-sub : ∀ {m n} {ρ ρ' : Subst m n} (i : Fin n) →
              ρ ≈βη ρ' → lookup i ρ ~βη lookup i ρ'
lookup-sub ()      ⋄
lookup-sub zero    (ext t~u ρ≈ρ') = t~u
lookup-sub (suc i) (ext _   ρ≈ρ') = lookup-sub i ρ≈ρ'

cong-[] : ∀ {m n} {t t' : Tm n} {ρ ρ' : Subst m n} →
           t ~βη t' →
           ρ ≈βη ρ' →
           t [ ρ ] ~βη t' [ ρ' ]
cong-[] (varcong i)           ρ≈ρ' = lookup-sub i ρ≈ρ'
cong-[] (apcong t~t' t~t'')   ρ≈ρ' = apcong (cong-[] t~t' ρ≈ρ') (cong-[] t~t'' ρ≈ρ')
cong-[] (ξ t~t')              ρ≈ρ' = ξ (cong-[] t~t' {!!})
cong-[] (sym~βη t~t')         ρ≈ρ' = sym~βη (cong-[] t~t' (sym≈βη ρ≈ρ'))
cong-[] (trans~βη t~t' t~t'') ρ≈ρ' = trans~βη (cong-[] t~t' ρ≈ρ') (cong-[] t~t'' refl≈βη)
cong-[] β                     ρ≈ρ' = {!!}
cong-[] η                     ρ≈ρ' = {!!}

cong-∘ : ∀ {m n k} {ρ σ : Subst m n} {ρ' σ' : Subst k m} →
          ρ  ≈βη σ →
          ρ' ≈βη σ' →
          ρ ∘ ρ' ≈βη σ ∘ σ'
cong-∘ ⋄           ρ'~σ'         = ⋄
cong-∘ (ext t ρ≈σ) ⋄             = ext (cong-[] t ⋄) (cong-∘ ρ≈σ ⋄)
cong-∘ (ext t ρ≈σ) (ext u ρ'≈σ') = ext (cong-[] t (ext u ρ'≈σ')) (cong-∘ ρ≈σ (ext u ρ'≈σ'))
