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

infix 7 _~βη_
infix 7 _~~βη_

data _~βη_  {n : Nat} : (_ _ : Term n) → Set where

  varcong   : (i : Fin n) → var i ~βη var i
  
  apcong    : {t u t′ u′ : Term n} →
               t ~βη t′ →
               u ~βη u′ →
               t · u ~βη t′ · u′
               
  ξ         : {t u : Term (1 + n)} →
               t ~βη u →
               ƛ t ~βη ƛ u
               
  β         : (t : Term (1 + n)) (u : Term n) →
               ƛ t · u ~βη t [ id ∙ u ]
               
  η         : (t : Term n) → ƛ (weaken t · q) ~βη t
  
  sym~βη    : {t₁ t₂ : Term n} →
               t₁ ~βη t₂ →
               t₂ ~βη t₁
               
  trans~βη  : {t₁ t₂ t₃ : Term n} →
               t₁ ~βη t₂ →
               t₂ ~βη t₃ →
               t₁ ~βη t₃

data _~~βη_ {m} : ∀ {n} (_ _ : Subst m n) → Set where

  ⋄   : ∀ {ρ ρ' : Subst m 0} → ρ ~~βη ρ'

  ext : ∀ {n} {t u : Term m} {ρ ρ' : Subst m n} →
         t ~βη u →
         ρ ~~βη ρ' →
         (ρ ∙ t) ~~βη (ρ' ∙ u)

-- Reflexivity is derived giving rise to _~βη_ as an equivalence relation

refl~βη : ∀ {n} {t : Term n} → t ~βη t
refl~βη {t = t} = trans~βη (sym~βη (η t)) (η t)

refl~~βη : ∀ {m n} {ρ : Subst m n} → ρ ~~βη ρ
refl~~βη {ρ = []}    = ⋄
refl~~βη {ρ = x ∷ ρ} = ext refl~βη refl~~βη

sym~~βη : ∀ {m n} {ρ ρ' : Subst m n} → ρ ~~βη ρ' → ρ' ~~βη ρ
sym~~βη ⋄ = ⋄
sym~~βη (ext x ρ~ρ') = ext (sym~βη x) (sym~~βη ρ~ρ')

trans~~βη : ∀ {m n} {ρ₁ ρ₂ ρ₃ : Subst m n} → ρ₁ ~~βη ρ₂ → ρ₂ ~~βη ρ₃ → ρ₁ ~~βη ρ₃
trans~~βη ⋄ _ = ⋄
trans~~βη (ext x ρ₁~ρ₂) (ext y ρ₂~ρ₃) = ext (trans~βη x y) (trans~~βη ρ₁~ρ₂ ρ₂~ρ₃)

~βηequiv : ∀ {n} → IsEquivalence (_~βη_ {n})
~βηequiv = record { refl  = refl~βη
                ; sym   = sym~βη
                ; trans = trans~βη }

-- Instance of setoid for Term under _~βη_

TermSetoid : ∀ {n} → Setoid _ _ 
TermSetoid {n} = record { Carrier = Term n
                        ; _≈_ = _~βη_
                        ; isEquivalence = ~βηequiv }

_≈⟨⟩_ : ∀ {n} → (t {u} : Term n) → t ~βη u → t ~βη u
t ≈⟨⟩ t~βηu = t~βηu

cong≡~βη : ∀ {n} {A : Set} {t u} (f : A → Term n) → t ≡ u → f t ~βη f u
cong≡~βη f refl = refl~βη

subst≡ : ∀ {n} {t u : Term n} → t ≡ u → t ~βη u
subst≡ refl = refl~βη

cong-∙ : ∀ {m n} {t t' : Term n} {ρ ρ' : Subst n m} →
          t ~βη t' →
          ρ ~~βη ρ' →
          (ρ ∙ t) ~~βη (ρ' ∙ t')
cong-∙ t~t' ⋄            = ext t~t' ⋄
cong-∙ t~t' (ext x ρ~ρ') = ext t~t' (cong-∙ x ρ~ρ')         

lookup-sub : ∀ {m n} {ρ ρ' : Subst m n} (i : Fin n) →
              ρ ~~βη ρ' →
              lookup i ρ ~βη lookup i ρ'
lookup-sub ()      ⋄
lookup-sub zero    (ext t~u ρ~ρ') = t~u
lookup-sub (suc i) (ext _   ρ~ρ') = lookup-sub i ρ~ρ'

postulate cong~~βη : ∀ {m n k p} {ρ ρ' : Subst m n} (f : Subst m n → Subst k p) → ρ ~~βη ρ' → f ρ ~~βη f ρ' 

cong-[] : ∀ {m n} {t t' : Term n} {ρ ρ' : Subst m n} →
           t ~βη t' →
           ρ ~~βη ρ' →
           t [ ρ ] ~βη t' [ ρ' ]
cong-[] (varcong i)           ρ~ρ' = lookup-sub i ρ~ρ'
cong-[] (apcong t~t' t~t'')   ρ~ρ' = apcong (cong-[] t~t' ρ~ρ') (cong-[] t~t'' ρ~ρ')
cong-[] (ξ t~t')              ρ~ρ' = ξ (cong-[] t~t' (cong~~βη ↑ₛ_ ρ~ρ'))
cong-[] (sym~βη t~t')         ρ~ρ' = sym~βη (cong-[] t~t' (sym~~βη ρ~ρ'))
cong-[] (trans~βη t~t' t~t'') ρ~ρ' = trans~βη (cong-[] t~t' ρ~ρ') (cong-[] t~t'' refl~~βη)
cong-[] {ρ = ρ} {ρ'} (β t u)  ρ~ρ' = sym~βη {!!}
cong-[] (η t)                 ρ~ρ' = {!!}

cong-⋆ : ∀ {m n k} {ρ σ : Subst m n} {ρ' σ' : Subst k m} →
          ρ ~~βη σ →
          ρ' ~~βη σ' →
          ρ ⋆ ρ' ~~βη σ ⋆ σ'
cong-⋆ ⋄           ρ'~σ'         = ⋄
cong-⋆ (ext x ρ~σ) ⋄             = ext (cong-[] x ⋄) (cong-⋆ ρ~σ ⋄)
cong-⋆ (ext x ρ~σ) (ext y ρ'~σ') = ext (cong-[] x (ext y ρ'~σ')) (cong-⋆ ρ~σ (ext y ρ'~σ'))
