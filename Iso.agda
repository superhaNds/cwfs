module Iso where

open import Function using (id ; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; trans ; sym)

record _≅_ (A B : Set) : Set₁ where
  field
    to    : A → B
    from  : B → A
    inv₁  : ∀ (a : A) → a ≡ from (to a)
    inv₂  : ∀ (b : B) → b ≡ to (from b)

ref≅ : ∀ {A} → A ≅ A
ref≅ = record { to   = id
              ; from = id
              ; inv₁ = λ _ → refl
              ; inv₂ = λ _ → refl }

sym≅ : ∀ {A B} → A ≅ B → B ≅ A
sym≅ record { to = f ; from = g ; inv₁ = φ; inv₂ = ψ }
  = record { to   = g
           ; from = f
           ; inv₁ = ψ
           ; inv₂ = φ }

trans≅ : ∀ {A B C} → A ≅ B → B ≅ C → A ≅ C
trans≅ record { to = f₁ ; from = g₁ ; inv₁ = φ₁ ; inv₂ = ψ₁ }
       record { to = f₂ ; from = g₂ ; inv₁ = φ₂ ; inv₂ = ψ₂ }
  = record { to   = f₂ ∘ f₁
           ; from = g₁ ∘ g₂
           ; inv₁ = λ a → trans (φ₁ a) (cong g₁ (φ₂ (f₁ a)))
           ; inv₂ = λ c → trans (ψ₂ c) (cong f₂ (ψ₁ (g₂ c))) }
