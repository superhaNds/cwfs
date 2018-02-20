module Ext-Typed.STyped.ScwfObj where

open import Data.Product
open import Data.Nat renaming (ℕ to Nat)
open import Agda.Primitive
open import Relation.Binary

record Scwf : Set₁ where
  infix 5 _⊢_∈_
  infix 5 _▹_⊢_
  field
    RTm  : Nat → Set
    RSub : Nat → Nat → Set
    _≈_  : ∀ {n} → Rel (RTm n) lzero
    _≋_  : ∀ {m n} → Rel (RSub m n) lzero

    --- ... remaining raw stuff
    
    -- Types
    Ty : Set

    -- Contexts
    Ctx : Nat → Set
    ε   : Ctx 0
    _∙_ : ∀ {n} → Ctx n → Ty → Ctx (suc n)

    -- typing relation - terms
    _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : RTm n) (α : Ty) → Set

    -- typing relation - substitutions
    _▹_⊢_ : ∀ {m n} (Γ : Ctx n) (Δ : Ctx m) (ρ : RSub n m) → Set

    -- sigma pairs of raw with typing rule

    -- identitiy
    id-ty : ∀ {n} {Γ : Ctx n} → Σ (RSub n n) (Γ ▹ Γ ⊢_)

    -- composition
    _∘_ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
          → Σ (RSub n k) (Γ ▹ Θ ⊢_)
          → Σ (RSub m n) (Δ ▹ Γ ⊢_)
          → Σ (RSub m k) (Δ ▹ Θ ⊢_)

    -- last variable
    q-ty  : ∀ {n} {Γ : Ctx n} {α} → Σ (RTm (suc n)) (Γ ∙ α ⊢_∈ α)

    -- projection substitution
    p-ty  : ∀ {n} {Γ : Ctx n} {α} → Σ (RSub (suc n) n) (Γ ∙ α ▹ Γ ⊢_)

    -- empty substitution
    <>-ty : ∀ {n} {Γ : Ctx n} → Σ (RSub n 0) (Γ ▹ ε ⊢_)

    -- extend substitution
    <,>-ty : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {t : RTm m} {α}
             → Σ (RSub m n) (Δ ▹ Γ ⊢_)
             → Σ (RTm m) (Δ ⊢_∈ α)
             → Σ (RSub m (suc n)) (Δ ▹ Γ ∙ α ⊢_)

    -- substitution operation
    sub-ty : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {α}
             → Σ (RTm n) (Γ ⊢_∈ α)
             → Σ (RSub m n) (Δ ▹ Γ ⊢_)
             → Σ (RTm m) (Δ ⊢_∈ α)


record Lambda-Scwf : Set₁ where
  field
    scwf : Scwf
  open Scwf scwf public
  field

    -- function type
    _`→_ : Ty → Ty → Ty

    -- λ abstraction
    lam-ty : ∀ {n} {Γ : Ctx n} {α β}
             → Σ (RTm (suc n)) (Γ ∙ α ⊢_∈ β)
             → Σ (RTm n) (Γ ⊢_∈ (α `→ β))

    -- application
    app-ty : ∀ {n} {Γ : Ctx n} {α β}
             → Σ (RTm n) (Γ ⊢_∈ (α `→ β))
             → Σ (RTm n) (Γ ⊢_∈ α)
             → Σ (RTm n) (Γ ⊢_∈ β)
