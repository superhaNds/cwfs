module Unityped.Wellscoped.Typed.Scwf where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product using (Σ)

record Scwf : Set₁ where
  infix 4 _⊢_∈_
  infix 4 _▹_⊢_
  field
    Type   : Set    
    RTm    : Nat → Set    
    Ctxt   : Nat → Set
    ε      : Ctxt 0
    _,_    : ∀ {n} → Ctxt n → Type → Ctxt (suc n)    
    Subst  : Nat → Nat → Set    
    _⊢_∈_  : ∀ {n} → Ctxt n → RTm n → Type → Set    
    _▹_⊢_  : ∀ {n m} → Ctxt m → Ctxt n → Subst n m → Set        
    sub   : ∀ {m n α} {Δ : Ctxt m} {Γ : Ctxt n} → Σ (RTm n) (Γ ⊢_∈ α) → Σ (Subst m n) (Γ ▹ Δ ⊢_) →
             Σ (RTm m) (Δ ⊢_∈ α)
    <> : ∀ {m} {Δ : Ctxt m} → Σ (Subst m 0) (ε ▹ Δ ⊢_)
    <_,_>  : ∀ {m n α} {Γ : Ctxt m} {Δ : Ctxt n} → Σ (Subst m n) (Δ ▹ Γ ⊢_) → Σ (RTm m) (Γ ⊢_∈ α) →
             Σ (Subst m (suc n)) (Δ , α ▹ Γ ⊢_)             
    _∘_    : ∀ {m n k} {Γ : Ctxt n} {Δ : Ctxt m} {Θ : Ctxt k} →
             Σ (Subst n k) (Θ ▹ Γ ⊢_) → Σ (Subst m n) (Γ ▹ Δ ⊢_) → Σ (Subst m k) (Θ ▹ Δ ⊢_)            
    p      : ∀ {n α} {Γ : Ctxt n} → Σ (Subst (suc n) n) (Γ ▹ Γ , α ⊢_)
    q      : ∀ {n α} {Γ : Ctxt n} → Σ (RTm (suc n)) (Γ , α ⊢_∈ α)

record Lambda-Scwf : Set₁ where
  field
    scwf : Scwf
  open Scwf scwf
  field
    _`→_ : Type → Type → Type
    app  : ∀ {n α β} {Γ : Ctxt n} → Σ (RTm n) (Γ ⊢_∈ (α `→ β)) →
           Σ (RTm n) (Γ ⊢_∈ α) → Σ (RTm n) (Γ ⊢_∈ β)
    ƛ : ∀ {n α β} {Γ : Ctxt n} → Σ (RTm (suc n)) (Γ , α ⊢_∈ β) →
        Σ (RTm n) (Γ ⊢_∈ (α `→ β))
