{-# OPTIONS --allow-unsolved-metas  #-}
---------------------------------------------------------------------
-- A relation for β conversion for the lambda calculus and
-- setoid definition. The isomorphism between cwf terms and
-- untyped lambda calculus terms is on this setoid.
---------------------------------------------------------------------

module Unityped.Wellscoped.Beta where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_])
open import Function as Fun using (_∘_ ; _$_ ; flip)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Unityped.Wellscoped.Syntax
open import Unityped.Wellscoped.Substitution
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality hiding ([_])

---------------------------------------------------------------------
-- β convertability as an inductive relation over terms

infix 9 _~β_

data _~β_  {n : Nat} : (_ _ : Term n) → Set where
  varcong : (i : Fin n) → var i ~β var i
  apcong  : {t u t′ u′ : Term n} → t ~β t′ → u ~β u′ → t · u ~β t′ · u′
  ξ       : {t u : Term (1 + n)} → t ~β u → ƛ t ~β ƛ u
  β       : (t : Term (1 + n)) (u : Term n) → ƛ t · u ~β t [ id ∙ u ]
  η       : (t : Term n) → ƛ (weaken t · q) ~β t
  sym~β    : {t₁ t₂ : Term n} → t₁ ~β t₂ → t₂ ~β t₁
  trans~β  : {t₁ t₂ t₃ : Term n} → t₁ ~β t₂ → t₂ ~β t₃ → t₁ ~β t₃

data _~~β_ : ∀ {n m} (_ _ : Subst m n) → Set where
  ⋄   : ∀ {m} {ρ ρ' : Subst m 0} → ρ ~~β ρ'
  ext : ∀ {m n} {t u : Term m} {ρ ρ' : Subst m n} → t ~β u → ρ ~~β ρ' → (ρ ∙ t) ~~β (ρ' ∙ u)

-- Reflexivity is derived giving rise to _~β_ as an equivalence relation

refl~β : ∀ {n} {t : Term n} → t ~β t
refl~β {t = t} = trans~β (sym~β (η t)) (η t)

~βequiv : ∀ {n} → IsEquivalence (_~β_ {n})
~βequiv = record { refl  = refl~β
                ; sym   = sym~β
                ; trans = trans~β }

-- Instance of setoid for Term under _~β_

TermSetoid : ∀ {n} → Setoid _ _ 
TermSetoid {n} = record { Carrier = Term n
                        ; _≈_ = _~β_
                        ; isEquivalence = ~βequiv }

_≈⟨⟩_ : ∀ {n} → (t {u} : Term n) → t ~β u → t ~β u
t ≈⟨⟩ t~βu = t~βu

cong≡~β : ∀ {n} {A : Set} {t u} (f : A → Term n) → t ≡ u → f t ~β f u
cong≡~β f refl = refl~β

subst≡ : ∀ {n} {t u : Term n} → t ≡ u → t ~β u
subst≡ refl = refl~β

{-
cong-[] : ∀ {m n} {t t' : Term n} {ρ ρ' : Subst m n} →
          t ~β t' → ρ ≡ ρ' → t [ ρ ] ~β t' [ ρ' ]
cong-[] (varcong i) refl = refl~β
cong-[] (apcong t~βt' t~βt'') φ =
  apcong (cong-[] t~βt' φ)
         (cong-[] t~βt'' φ)
cong-[] (ξ t~βt') refl = ξ (cong-[] t~βt' refl)
cong-[] (sym~β t~βt') refl =
  sym~β (cong-[] t~βt' refl)
cong-[] (trans~β t~βt' t~βt'') refl =
  trans~β (cong-[] t~βt' refl)
         (cong-[] t~βt'' refl)
cong-[] (β t u) refl = {!!}
cong-[] (η t) refl = {!!}

cong-⋆ : ∀ {m n k} {ρ σ : Subst m n} {ρ' σ' : Subst k m} →
         ρ ≡ σ → ρ' ≡ σ' → ρ ⋆ ρ' ≡ σ ⋆ σ'
cong-⋆ refl refl = refl

cong-∙ : ∀ {m n} {t t' : Term n} {ρ ρ' : Subst n m} →
         t ~β t' → ρ ≡ ρ' → ρ ∙ t ≡ ρ' ∙ t'
cong-∙ (varcong i) refl = refl
cong-∙ {ρ = ρ} (apcong t~βt' t~βt'') φ
  with cong-∙ {ρ = ρ} t~βt' φ
     | cong-∙ {ρ = ρ} t~βt'' φ
... | refl | refl = refl
cong-∙ (ξ t~βt') refl
  with cong-∙ {ρ = []} t~βt' refl
... | refl = refl
cong-∙ (sym~β t~βt') refl =
  sym (cong-∙ t~βt' refl)
cong-∙ (trans~β t~βt' t~βt'') refl =
  trans (cong-∙ t~βt' refl)
        (cong-∙ t~βt'' refl)
cong-∙ (β t u) refl = {!!}
cong-∙ (η t) refl = {!!}
-}
