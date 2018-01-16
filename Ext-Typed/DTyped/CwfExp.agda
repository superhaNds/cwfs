module Ext-Typed.DTyped.CwfExp where


data Ctx : Set
data Sub : Ctx → Ctx → Set

data Ty : Ctx → Set
data _⊢_ : (Γ : Ctx) (Λ : Ty Γ) → Set


data Ctx where
  ⋄   : Ctx
  _,_ : ∀ Γ → Ty Γ → Ctx



data Ty where

  _[_]T : ∀ {Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ




data Sub where

  id : ∀ {Γ} → Sub Γ Γ

  _∘_ : ∀ {Θ Δ Γ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ

  <> : ∀ {Γ} → Sub Γ ⋄

  <_,_> : ∀ {Δ Γ} (A : Ty Γ) (γ : Sub Δ Γ)
            (t : Δ ⊢ (A [ γ ]T))
          → Sub Δ (Γ , A)

  p : ∀ {Γ} {A : Ty Γ} → Sub (Γ , A) Γ


data _⊢_ where

  q : ∀ {Γ} (A : Ty Γ) → (Γ , A) ⊢ (A [ p ]T)

  _[_] : ∀ {Δ Γ} (A : Ty Γ) (t : Γ ⊢ A) (γ : Sub Δ Γ) → Δ ⊢ (A [ γ ]T)
