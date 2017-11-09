module SimpTyped.Tm.Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin hiding (_≤?_ ; _+_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SimpTyped.Tm.Type
open import SimpTyped.Tm.Context
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤)

Ctx : Set
Ctx = Ctxt Ty

data Term (Γ : Ctx) : Ty → Set where
  var : ∀ {α} (∈Γ : α ∈ Γ) → Term Γ α
  _·_ : ∀ {α β} → Term Γ (α ⇒ β) → Term Γ α → Term Γ β
  ƛ   : ∀ α {β} → Term (Γ , α) β → Term Γ α → Term Γ (α ⇒ β)
