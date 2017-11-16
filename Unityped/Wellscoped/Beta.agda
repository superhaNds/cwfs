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

infix 9 _~_

data _~_  {n : Nat} : (t u : Term n) → Set where
  varcong : (i : Fin n) → var i ~ var i
  apcong  : {t u t′ u′ : Term n} → t ~ t′ → u ~ u′ → t · u ~ t′ · u′
  ξ       : {t u : Term (1 + n)} → t ~ u → ƛ t ~ ƛ u
  β       : (t : Term (1 + n)) (u : Term n) → ƛ t · u ~ t [ id ∙ u ]
  η       : (t : Term n) → ƛ (weakenₛ t · q) ~ t
  sym~    : {t₁ t₂ : Term n} → t₁ ~ t₂ → t₂ ~ t₁
  trans~  : {t₁ t₂ t₃ : Term n} → t₁ ~ t₂ → t₂ ~ t₃ → t₁ ~ t₃

-- Reflexivity is derived giving rise to _~_ as an equivalence relation

refl~ : ∀ {n} {t : Term n} → t ~ t
refl~ {t = t} = trans~ (sym~ (η t)) (η t)

~equiv : ∀ {n} → IsEquivalence (_~_ {n})
~equiv = record { refl  = refl~
                ; sym   = sym~
                ; trans = trans~ }

-- Instance of setoid for Term under _~_

TermSetoid : ∀ {n} → Setoid _ _ 
TermSetoid {n} = record { Carrier = Term n
                        ; _≈_ = _~_
                        ; isEquivalence = ~equiv }

_≈⟨⟩_ : ∀ {n} → (t {u} : Term n) → t ~ u → t ~ u
t ≈⟨⟩ t~u = t~u

cong≡~ : ∀ {n} {A : Set} {t u} (f : A → Term n) → t ≡ u → f t ~ f u
cong≡~ f refl = refl~

subst≡ : ∀ {n} {t u : Term n} → t ≡ u → t ~ u
subst≡ refl = refl~

{-
cong-[] : ∀ {m n} {t t' : Term n} {ρ ρ' : Subst m n} →
          t ~ t' → ρ ≡ ρ' → t [ ρ ] ~ t' [ ρ' ]
cong-[] (varcong i) refl = refl~
cong-[] (apcong t~t' t~t'') φ =
  apcong (cong-[] t~t' φ)
         (cong-[] t~t'' φ)
cong-[] (ξ t~t') refl = ξ (cong-[] t~t' refl)
cong-[] (sym~ t~t') refl =
  sym~ (cong-[] t~t' refl)
cong-[] (trans~ t~t' t~t'') refl =
  trans~ (cong-[] t~t' refl)
         (cong-[] t~t'' refl)
cong-[] (β t u) refl = {!!}
cong-[] (η t) refl = {!!}

cong-⋆ : ∀ {m n k} {ρ σ : Subst m n} {ρ' σ' : Subst k m} →
         ρ ≡ σ → ρ' ≡ σ' → ρ ⋆ ρ' ≡ σ ⋆ σ'
cong-⋆ refl refl = refl

cong-∙ : ∀ {m n} {t t' : Term n} {ρ ρ' : Subst n m} →
         t ~ t' → ρ ≡ ρ' → ρ ∙ t ≡ ρ' ∙ t'
cong-∙ (varcong i) refl = refl
cong-∙ {ρ = ρ} (apcong t~t' t~t'') φ
  with cong-∙ {ρ = ρ} t~t' φ
     | cong-∙ {ρ = ρ} t~t'' φ
... | refl | refl = refl
cong-∙ (ξ t~t') refl
  with cong-∙ {ρ = []} t~t' refl
... | refl = refl
cong-∙ (sym~ t~t') refl =
  sym (cong-∙ t~t' refl)
cong-∙ (trans~ t~t' t~t'') refl =
  trans (cong-∙ t~t' refl)
        (cong-∙ t~t'' refl)
cong-∙ (β t u) refl = {!!}
cong-∙ (η t) refl = {!!}
-}
