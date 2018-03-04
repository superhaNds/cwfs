module Ext-Typed.STyped.ExtScwf where

open import Data.Product
open import Data.Nat renaming (ℕ to Nat)
open import Agda.Primitive
open import Relation.Binary
open import Unityped.Ucwf

record Scwf : Set₁ where
  infix 5 _⊢_∈_
  infix 5 _▹_⊢_
  field
    ucwf : Ucwf
  open Ucwf ucwf renaming (Tm to RTm ; Sub to RSub)
  field
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
    ∘-ty : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
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
  open Ucwf ucwf renaming (Tm to RTm)
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
