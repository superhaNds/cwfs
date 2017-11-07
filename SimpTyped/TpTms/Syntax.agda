module Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin hiding (_≤?_ ; _+_)
open import Relation.Nullary.Decidable
open import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Type

Ctx : Nat → Set
Ctx = Vec Ty

_,_ : ∀ {n} {A : Set} → Vec A n → A → Vec A (suc n)
Γ , α = α ∷ Γ

data Term {n} (Γ : Ctx n) : Ty → Set where
  var : (i : Fin n) → Term Γ (lookup i Γ)
  _·_ : ∀ {α β} → Term Γ (α ⇒ β) → Term Γ α → Term Γ β
  ƛ   : ∀ α {β} → Term (Γ , α) β → Term Γ α → Term Γ (α ⇒ β)
