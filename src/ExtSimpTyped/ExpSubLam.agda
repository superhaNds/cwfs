module ExtSimpTyped.ExpSubLam where

open import Unityped.ExpSubLam renaming (Tm to RTm ; Sub to RSub)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product using (Σ ; _,_)
open import ExtSimpTyped.Scwf
open import ExtSimpTyped.CtxType

infix 4 _⊢_∈_
infix 4 _⊢_∈s_

data _⊢_∈_ : ∀ {n} → Ctx n → RTm n → Ty → Set

data _⊢_∈s_ : ∀ {m n} → Ctx n → RSub m n → Ctx m → Set

data _⊢_∈_ where

  ⊢q : ∀ {n α} {Γ : Ctx n} → Γ ∙ α ⊢ q ∈ α

  ⊢sub : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {α t ρ}
         → Γ ⊢ t ∈ α
         → Γ ⊢ ρ ∈s Δ
         → Δ ⊢ t [ ρ ] ∈ α
         
  ⊢ƛ : ∀ {n t α β} {Γ : Ctx n}
       → Γ ∙ α ⊢ t ∈ β
       → Γ ⊢ ƛ t ∈ α ⇒ β

  ⊢app : ∀ {n t u σ τ} {Γ : Ctx n}
         → Γ ⊢ t ∈ σ ⇒ τ
         → Γ ⊢ u ∈ σ
         → Γ ⊢ app t u ∈ τ

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
private

  Σ-<> : ∀ {m} {Δ : Ctx m} → Σ (RSub m 0) (ε ⊢_∈s Δ)
  Σ-<> = <> , ⊢<>

  Σ-<,> : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
          → Σ (RSub m n) (Γ ⊢_∈s Δ)
          → Σ (RTm m) (Δ ⊢_∈ α)
          → Σ (RSub m (suc n)) (Γ ∙ α ⊢_∈s Δ)
  Σ-<,> (ρ , ⊢ρ) (t , ⊢t) = < ρ , t > , ⊢<,> ⊢t ⊢ρ

  Σ-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
        → Σ (RSub m n) (Γ ⊢_∈s Δ)
        → Σ (RSub k m) (Δ ⊢_∈s Θ)
        → Σ (RSub k n) (Γ ⊢_∈s Θ)
  Σ-∘ (ρ , ⊢ρ) (σ , ⊢σ) = (ρ ∘ σ) , ⊢∘ ⊢ρ ⊢σ

  Σ-sub : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
          → Σ (RTm m) (Δ ⊢_∈ α)
          → Σ (RSub n m) (Δ ⊢_∈s Γ)
          → Σ (RTm n) (Γ ⊢_∈ α)
  Σ-sub (t , ⊢t) (ρ , ⊢ρ) = (t [ ρ ]) , ⊢sub ⊢t ⊢ρ

  Σ-id : ∀ {n} {Γ : Ctx n} → Σ (RSub n n) (Γ ⊢_∈s Γ)
  Σ-id = id , ⊢id

  Σ-p : ∀ {n α} {Γ : Ctx n} → Σ (RSub (suc n) n) (Γ ⊢_∈s Γ ∙ α)
  Σ-p = p , ⊢p

  Σ-q : ∀ {n α} {Γ : Ctx n} → Σ (RTm (suc n)) (Γ ∙ α ⊢_∈ α)
  Σ-q = q , ⊢q

  ExpSubLamScwf : λβη-scwf
  ExpSubLamScwf = record
                 { λucwf  = ExpSubLamUcwf
                 ; Ty     = Ty
                 ; _`→_   = _⇒_
                 ; Ctx    = Ctx
                 ; ε      = ε
                 ; _∙_    = _∙_
                 ; _⊢_∈_  = _⊢_∈_
                 ; _⊢_∈s_ = _⊢_∈s_
                 ; Σ-<>   = <> , ⊢<>
                 ; Σ-<,>  = Σ-<,>
                 ; Σ-∘    = Σ-∘
                 ; Σ-sub  = Σ-sub
                 ; Σ-id   = id , ⊢id
                 ; Σ-p    = p , ⊢p
                 ; Σ-q    = q , ⊢q
                 ; Σ-lam  = λ { (t , ⊢t) → ƛ t , ⊢ƛ ⊢t }
                 ; Σ-app  = λ { (t , ⊢t) (u , ⊢u) → app t u , ⊢app ⊢t ⊢u }
                 }

