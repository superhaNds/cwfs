module Unityped.Wellscoped.Typed.Scwf where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product using (Σ)

record ScwfR : Set₁ where
  field
    Type   : Set
    
    RTm    : Nat → Set
    
    Ctxt   : Nat → Set
    
    _,_    : ∀ {n} → Ctxt n → Type → Ctxt (suc n)
    
    Subst  : Nat → Nat → Set
    
    _⊢_∈_  : ∀ {n} → Ctxt n → RTm n → Type → Set
    
    Tm     : ∀ {n} (Γ : Ctxt n) (α : Type) → Σ (RTm n) (Γ ⊢_∈ α)
    
    _▹_⊢_  : ∀ {n m} → Ctxt m → Ctxt n → Subst m n → Set
    
    Sb     : ∀ {m n} (Γ : Ctxt n) (Δ : Ctxt m) → Σ (Subst m n) (Δ ▹ Γ ⊢_)
    
    --_[_]   : ∀ {m n α} {Δ : Ctxt m} {Γ : Ctxt n} → Tm Γ α → Sb Γ Δ → Tm Δ α
    --`<_,_> : ∀ {Γ Δ α} → Sb Γ Δ → Tm Γ α → Sb Γ (Δ , α)
    --_∘_    : ∀ {Γ Δ Θ} → Sb Γ Θ → Sb Δ Γ → Sb Δ Θ
    -- p     : ∀ {Γ α} → Sb (Γ , α) Γ
    -- q     : ∀ {Γ α} → Tm (Γ , α) α
