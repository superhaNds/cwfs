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
import Relation.Binary.PropositionalEquality as P

---------------------------------------------------------------------
-- β convertability as an inductive relation over terms

infix 9 _~_

data _~_  {n : Nat} : (t u : Term n) → Set where
  varcong : (i : Fin n) → var i ~ var i
  apcong  : {t u t′ u′ : Term n} → t ~ t′ → u ~ u′ → t · u ~ t′ · u′
  ξ       : (t u : Term (1 + n)) → t ~ u → ƛ t ~ ƛ u
  β       : (t : Term (1 + n)) (u : Term n) → ƛ t · u ~ t [ id ∙ u ]
  η       : (t : Term n) → ƛ (weakenₛ t · q) ~ t
  sym~    : {t₁ t₂ : Term n} → t₁ ~ t₂ → t₂ ~ t₁
  trans~  : {t₁ t₂ t₃ : Term n} → t₁ ~ t₂ → t₂ ~ t₃ → t₁ ~ t₃
  cong~   : ∀ {m} {t u} (f : Term m → Term n) → t ~ u → f t ~ f u 

-- Reflexivity is derived giving rise to _~_ as an equivalence relation

refl~ : ∀ {n} {t : Term n} → t ~ t
refl~ {n} {t} = trans~ (sym~ (η t)) (η t)

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
_ ≈⟨⟩ t~u = t~u

cong≡~ : ∀ {n} {A : Set} {t u} (f : A → Term n) → t P.≡ u → f t ~ f u
cong≡~ f P.refl = refl~
