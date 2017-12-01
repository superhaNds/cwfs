module Unityped.Wellscoped.Typed.ScwfDirect where

open import Data.Nat renaming (ℕ to Nat)

record DScwf : Set₁ where
  field
    Ty : Set
    Ctx : Nat → Set
    _,_ : ∀ {n} → Ctx n → Ty → Ctx (suc n)
    ε : Ctx 0
    Tm  : ∀ {n} → Ctx n → Ty → Set
    Hom : ∀ {m n} → Ctx m → Ctx n → Set


    <>    : ∀ {n} {Γ : Ctx n} → Hom ε Γ
    id    : ∀ {n} {Γ : Ctx n} → Hom Γ Γ
    p     : ∀ {n α} {Γ : Ctx n} → Hom Γ (Γ , α)
    q     : ∀ {n α} {Γ : Ctx n} → Tm (Γ , α) α
    _∘_   : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} →
            Hom Γ Θ → Hom Δ Γ → Hom Δ Θ
    _[_]  : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {α} →
            Tm Γ α → Hom Γ Δ → Tm Δ α
    <_,_> : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {α} →
            Hom Δ Γ → Tm Γ α → Hom (Δ , α) Γ
