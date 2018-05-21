module ExtSimpTyped.Scwf where

open import Data.Product
open import Data.Nat renaming (ℕ to Nat)
open import Agda.Primitive
open import Relation.Binary
open import Unityped.Ucwf

record Scwf : Set₁ where
  infix 5 _⊢_∈_
  infix 5 _⊢_∈s_
  field
    ucwf : Ucwf
  open Ucwf ucwf renaming (Tm to RTm ; Sub to RSub)
  field
    Ty : Set
    
    Ctx : Nat → Set
    ε   : Ctx 0
    _∙_ : ∀ {n} → Ctx n → Ty → Ctx (suc n)

    _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : RTm n) (α : Ty) → Set

    _⊢_∈s_ : ∀ {m n} (Γ : Ctx n) (ρ : RSub m n) (Δ : Ctx m) → Set    

    Σ-<> : ∀ {m} {Δ : Ctx m} → Σ (RSub m 0) (ε ⊢_∈s Δ)

    Σ-<,> : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
            → Σ (RSub m n) (Γ ⊢_∈s Δ)
            → Σ (RTm m) (Δ ⊢_∈ α)
            → Σ (RSub m (suc n)) (Γ ∙ α ⊢_∈s Δ)

    Σ-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
          → Σ (RSub m n) (Γ ⊢_∈s Δ)
          → Σ (RSub k m) (Δ ⊢_∈s Θ)
          → Σ (RSub k n) (Γ ⊢_∈s Θ)

    Σ-sub : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
            → Σ (RTm m) (Δ ⊢_∈ α)
            → Σ (RSub n m) (Δ ⊢_∈s Γ)
            → Σ (RTm n) (Γ ⊢_∈ α)

    Σ-id : ∀ {n} {Γ : Ctx n} → Σ (RSub n n) (Γ ⊢_∈s Γ)

    Σ-p : ∀ {n α} {Γ : Ctx n} → Σ (RSub (suc n) n) (Γ ⊢_∈s Γ ∙ α)

    Σ-q : ∀ {n α} {Γ : Ctx n} → Σ (RTm (suc n)) (Γ ∙ α ⊢_∈ α)

record λβη-scwf : Set₁ where
  infix 5 _⊢_∈_
  infix 5 _⊢_∈s_
  field
    λucwf : λβη-ucwf
  open λβη-ucwf λucwf 
  open Ucwf ucwf renaming (Tm to RTm ; Sub to RSub)
  field
    Ty   : Set
    _`→_ : Ty → Ty → Ty
    
    Ctx : Nat → Set
    ε   : Ctx 0
    _∙_ : ∀ {n} → Ctx n → Ty → Ctx (suc n)

    _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : RTm n) (α : Ty) → Set

    _⊢_∈s_ : ∀ {m n} (Γ : Ctx n) (ρ : RSub m n) (Δ : Ctx m) → Set    

    Σ-<> : ∀ {m} {Δ : Ctx m} → Σ (RSub m 0) (ε ⊢_∈s Δ)

    Σ-<,> : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
            → Σ (RSub m n) (Γ ⊢_∈s Δ)
            → Σ (RTm m) (Δ ⊢_∈ α)
            → Σ (RSub m (suc n)) (Γ ∙ α ⊢_∈s Δ)

    Σ-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
          → Σ (RSub m n) (Γ ⊢_∈s Δ)
          → Σ (RSub k m) (Δ ⊢_∈s Θ)
          → Σ (RSub k n) (Γ ⊢_∈s Θ)

    Σ-sub : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
            → Σ (RTm m) (Δ ⊢_∈ α)
            → Σ (RSub n m) (Δ ⊢_∈s Γ)
            → Σ (RTm n) (Γ ⊢_∈ α)

    Σ-id : ∀ {n} {Γ : Ctx n} → Σ (RSub n n) (Γ ⊢_∈s Γ)

    Σ-p : ∀ {n α} {Γ : Ctx n} → Σ (RSub (suc n) n) (Γ ⊢_∈s Γ ∙ α)

    Σ-q : ∀ {n α} {Γ : Ctx n} → Σ (RTm (suc n)) (Γ ∙ α ⊢_∈ α)

    Σ-lam : ∀ {n} {Γ : Ctx n} {α β}
            → Σ (RTm (suc n)) (Γ ∙ α ⊢_∈ β)
            → Σ (RTm n) (Γ ⊢_∈ (α `→ β))

    Σ-app : ∀ {n} {Γ : Ctx n} {α β}
            → Σ (RTm n) (Γ ⊢_∈ (α `→ β))
            → Σ (RTm n) (Γ ⊢_∈ α)
            → Σ (RTm n) (Γ ⊢_∈ β)
