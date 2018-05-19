module ExtSimpTyped.ExpSub where

open import Unityped.ExpSub renaming (_∙_ to _∘_ ; Tm to RTm ; Sub to RSub)
open import Data.Nat renaming (ℕ to Nat)

postulate Ty : Set

data Ctx : Nat →  Set where
  ε   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Ty → Ctx (suc n)

infix 4 _⊢_∈_
infix 4 _⊢_∈s_

data _⊢_∈_ : ∀ {n} → Ctx n → RTm n → Ty → Set

data _⊢_∈s_ : ∀ {m n} → Ctx n → RSub m n → Ctx m → Set

data _⊢_∈_ where

  ⊢q   : ∀ {n α} {Γ : Ctx n} → Γ ∙ α ⊢ q ∈ α

  ⊢sub : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {α t ρ}
         → Γ ⊢ t ∈ α
         → Γ ⊢ ρ ∈s Δ
         → Δ ⊢ t [ ρ ] ∈ α
         
data _⊢_∈s_ where

  ⊢<> : ∀ {m} {Δ : Ctx m} → ε ⊢ <> ∈s Δ

  ⊢id : ∀ {n} {Γ : Ctx n} → Γ ⊢ id ∈s Γ
  
  ⊢p  : ∀ {n α} {Γ : Ctx n} → Γ ⊢ p ∈s Γ ∙ α

  ⊢∘  : ∀ {m n k Γ Δ Θ} {ρ : RSub m n} {σ : RSub k m}
        → Θ ⊢ ρ ∈s Δ
        → Δ ⊢ σ ∈s Γ
        → Θ ⊢ ρ ∘ σ ∈s Γ
        
  ⊢<,> : ∀ {m n t α Γ Δ} {ρ : RSub m n}
         → Δ ⊢ t ∈ α
         → Γ ⊢ ρ ∈s Δ
         → Γ ∙ α ⊢ < ρ , t > ∈s Δ
