module Unityped.Wellscoped.Typed.ScwfDirectComb where

open import Data.Nat renaming (ℕ to Nat)
open import Unityped.Wellscoped.Typed.CtxType

data Tm : ∀ {n} (Γ : Ctx n) (α : Ty) → Set
data Subst : ∀ {n m} → Ctx m → Ctx n → Set

data Tm where
  q    : ∀ {n α} {Γ : Ctx n} → Tm (Γ , α) α
  _[_] : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {α} →
         Tm Γ α → Subst Γ Δ → Tm Δ α
data Subst where
  <>     : ∀ {n} {Γ : Ctx n} → Subst ε Γ
  id     : ∀ {n} {Γ : Ctx n} → Subst Γ Γ
  p      : ∀ {n α} {Γ : Ctx n} → Subst Γ (Γ , α)
  _∘_    : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} →
           Subst Θ Γ → Subst Δ Θ → Subst Δ Γ
  <_,_>  : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {α} →
           Subst Δ Γ → Tm Γ α → Subst (Δ , α) Γ
