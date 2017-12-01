module Unityped.Wellscoped.Typed.ScwfComb where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product using (Σ)
open import Data.Vec hiding ([_])
open import Unityped.Wellscoped.Typed.CtxType

data RTm : Nat → Set
data Subst : Nat → Nat → Set

data RTm where
  q    : ∀ {n} → RTm (suc n)
  _[_] : ∀ {m n} → RTm n → Subst m n → RTm m

data Subst where
  <>    : ∀ {m} → Subst m zero
  id    : ∀ {n} → Subst n n
  p     : ∀ {n} → Subst (suc n) n
  <_,_> : ∀ {m n} → Subst m n → RTm m → Subst m (suc n)
  _∘_   : ∀ {m n k} → Subst n k → Subst m n → Subst m k
  
infix 4 _⊢_∈_
infix 4 _▹_⊢_

data _⊢_∈_ : ∀ {n} → Ctx n → RTm n → Ty → Set

data _▹_⊢_ : ∀ {m n} → Ctx m → Ctx n → Subst n m → Set

data _⊢_∈_ where

  ⊢q   : ∀ {n α} {Γ : Ctx n} → Γ , α ⊢ q ∈ α

  []∈ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {α t ρ} →
  
        Γ ⊢ t ∈ α → Γ ▹ Δ ⊢ ρ →
        ------------------------
            Δ ⊢ t [ ρ ] ∈ α

data _▹_⊢_ where

  ⊢<> : ∀ {m} {Δ : Ctx m} → ε ▹ Δ ⊢ <>

  ⊢id : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ id
  
  ⊢p  : ∀ {n α} {Γ : Ctx n} → Γ ▹ Γ , α ⊢ p

  ⊢∘  : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
          {ρ : Subst k m} {ρ' : Subst n k} →
          
        Θ ▹ Γ ⊢ ρ' → Δ ▹ Θ ⊢ ρ → 
        -------------------------
             Δ ▹ Γ ⊢ ρ ∘ ρ'
  
  ⊢<,> : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
           {t : RTm m} {ρ : Subst m n} {α} →
         
         Δ ⊢ t ∈ α → Γ ▹ Δ ⊢ ρ →
         ------------------------
           Γ , α ▹ Δ ⊢ < ρ , t >

sub : ∀ {m n α} {Δ : Ctx m} {Γ : Ctx n} → Σ (RTm n) (Γ ⊢_∈ α) →
      Σ (Subst m n) (Γ ▹ Δ ⊢_) → Σ (RTm m) (Δ ⊢_∈ α)             
sub (t Σ., t∈) (ρ Σ., ⊢ρ) = t [ ρ ] Σ., []∈ t∈ ⊢ρ
