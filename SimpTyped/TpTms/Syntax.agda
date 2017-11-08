module Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin hiding (_≤?_ ; _+_)
open import Relation.Nullary.Decidable
open import Data.Vec as Vec hiding ([_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Type
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤)

Ctx : Nat → Set
Ctx = Vec Ty

_,_ : ∀ {n} {A : Set} → Vec A n → A → Vec A (suc n)
Γ , α = α ∷ Γ

data Term {n} (Γ : Ctx n) : Ty → Set where
  var : (i : Fin n) → Term Γ (lookup i Γ)
  _·_ : ∀ {α β} → Term Γ (α ⇒ β) → Term Γ α → Term Γ β
  ƛ   : ∀ α {β} → Term (Γ , α) β → Term Γ α → Term Γ (α ⇒ β)

Subst : ∀ {n m} (Γ : Ctx n) (Δ : Ctx m) → Set
Subst Γ [] = ⊤
Subst Γ (δ ∷ Δ) = Term Γ δ × Subst Γ Δ 

_[_] : ∀ {n m} {α} {Γ : Ctx n} {Δ : Ctx m} → Term Γ α → Subst Δ Γ → Term Δ α
t [ ρ ] = {!!}
