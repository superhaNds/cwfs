-------------------------------------------------------------------------------
-- The set of types
-------------------------------------------------------------------------------
module SimpTyped.Type where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤)
open import Function using (_∘_ ; _$_)
open import Data.Vec
open import Data.Nat using (ℕ)

-------------------------------------------------------------------------------
-- Types

infixr 20 _⇒_

data Ty : Set where
  ♭   : Ty
  _⇒_ : (α β : Ty) → Ty

eq⇒₁ : ∀ {α α′ β β′} → α ⇒ β ≡ α′ ⇒ β′ → α ≡ α′
eq⇒₁ refl = refl

eq⇒₂ : ∀ {α α′ β β′} → α ⇒ β ≡ α′ ⇒ β′ → β ≡ β′
eq⇒₂ refl = refl

-- Type equality is decidable

_≟_ : ∀ (α β : Ty) → Dec (α ≡ β)
♭       ≟ ♭       = yes refl
♭       ≟ (_ ⇒ _) = no $ λ ()
(_ ⇒ _) ≟ ♭       = no $ λ ()
(α ⇒ γ) ≟ (β ⇒ δ) with α ≟ β | γ ≟ δ
(α ⇒ γ) ≟ (_ ⇒ _) | yes refl | yes refl = yes refl
...               | no α≠β   | _        = no $ α≠β ∘ eq⇒₁
...               | _        | no γ≠δ   = no $ γ≠δ ∘ eq⇒₂

⟦_⟧ᵀ : (α : Ty) → Set
⟦ ♭ ⟧ᵀ       = ⊤
⟦ α₁ ⇒ α₂ ⟧ᵀ = ⟦ α₁ ⟧ᵀ → ⟦ α₂ ⟧ᵀ

----------------------------------------------------------------------------------
-- Contexts are well-scoped

Ctx : ℕ → Set
Ctx = Vec Ty
