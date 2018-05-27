module ExtSimpTyped.ImpSub where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec hiding ([_])
open import Data.Fin
open import Data.Product using (Σ)
open import Unityped.ImpSub renaming (_∙_ to _∘_)
open import ExtSimpTyped.Scwf

postulate Ty : Set

Ctx : Nat → Set
Ctx = Vec Ty

_∙_ : ∀ {n} (Γ : Ctx n) (α : Ty) → Ctx (suc n)
Γ ∙ α = α ∷ Γ

infix 4 _⊢_∈_
infix 4 _⊢_∈s_

data _⊢_∈_ {n} : Ctx n → Fin n → Ty → Set where
  ⊢var : ∀ {i Γ} → Γ ⊢ i ∈ lookup i Γ

data _⊢_∈s_ : ∀ {n m} → Ctx n → Ren m n → Ctx m → Set where
  ⊢[] : ∀ {m} {Δ : Ctx m} → [] ⊢ [] ∈s Δ
  
  ⊢,  : ∀ {m n} {Γ Δ α} {ρ : Ren m n} {i : Fin m}
        → Γ ⊢ ρ ∈s Δ
        → Δ ⊢ i ∈ α
        → Γ ∙ α ⊢ i ∷ ρ ∈s Δ

⊢q : ∀ {n α} {Γ : Ctx n} → Γ ∙ α ⊢ zero ∈ α
⊢q = ⊢var

map-suc-preserv : ∀ {m n Γ Δ α} (ρ : Ren m n)
                  → Γ ⊢ ρ ∈s Δ
                  → Γ ⊢ map suc ρ ∈s Δ ∙ α
map-suc-preserv [] ⊢[] = ⊢[]
map-suc-preserv (x ∷ ρ) (⊢, ⊢ρ ⊢var) = ⊢, (map-suc-preserv ρ ⊢ρ) ⊢var

↑-preserv : ∀ {m n Γ Δ α} {ρ : Ren m n}
            → Γ ⊢ ρ ∈s Δ
            → Γ ∙ α ⊢ ↑ ρ ∈s Δ ∙ α
↑-preserv ⊢ρ = ⊢, (map-suc-preserv _ ⊢ρ) ⊢var

id-preserv : ∀ {n} {Γ : Ctx n} → Γ ⊢ id ∈s Γ
id-preserv {Γ = []}    = ⊢[]
id-preserv {Γ = x ∷ Γ} = ↑-preserv id-preserv

p-preserv : ∀ {n α} {Γ : Ctx n} → Γ ⊢ p ∈s (Γ ∙ α)
p-preserv = map-suc-preserv id id-preserv

lookup-preserv : ∀ {m n Γ Δ} i (ρ : Ren m n)
                 → Γ ⊢ ρ ∈s Δ
                 → Δ ⊢ lookup i ρ ∈ lookup i Γ
lookup-preserv zero    (_ ∷ _) (⊢, _ ∈α) = ∈α
lookup-preserv (suc i) (_ ∷ ρ) (⊢, ⊢ρ _) = lookup-preserv i ρ ⊢ρ

/-preserv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {i ρ α}
            → Γ ⊢ i ∈ α
            → Γ ⊢ ρ ∈s Δ
            → Δ ⊢ i / ρ ∈ α
/-preserv (⊢var {i}) ⊢ρ = lookup-preserv i _ ⊢ρ

∘-preserv : ∀ {m n k} {Γ Δ Θ} {ρ : Ren m n} {σ : Ren k m}
            → Θ ⊢ ρ ∈s Δ
            → Δ ⊢ σ ∈s Γ
            → Θ ⊢ ρ ∘ σ ∈s Γ
∘-preserv ⊢[]        _  = ⊢[]
∘-preserv (⊢, ⊢ρ ⊢i) ⊢σ = ⊢, (∘-preserv ⊢ρ ⊢σ) (/-preserv ⊢i ⊢σ)

private

  Σ-[] : ∀ {m} {Δ : Ctx m} → Σ (Ren m 0) ([] ⊢_∈s Δ)
  Σ-[] = [] Σ., ⊢[]

  Σ-, : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
        → Σ (Ren m n) (Γ ⊢_∈s Δ)
        → Σ (Fin m) (Δ ⊢_∈ α)
        → Σ (Ren m (suc n)) (Γ ∙ α ⊢_∈s Δ)
  Σ-, (ρ Σ., ⊢ρ) (i Σ., ⊢i) = i ∷ ρ Σ., ⊢, ⊢ρ ⊢i      

  Σ-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
        → Σ (Ren m n) (Γ ⊢_∈s Δ)
        → Σ (Ren k m) (Δ ⊢_∈s Θ)
        → Σ (Ren k n) (Γ ⊢_∈s Θ)
  Σ-∘ (ρ Σ., ⊢ρ) (σ Σ., ⊢σ) = (ρ ∘ σ) Σ., (∘-preserv ⊢ρ ⊢σ)      

  Σ-/ : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
        → Σ (Fin m) (Δ ⊢_∈ α)
        → Σ (Ren n m) (Δ ⊢_∈s Γ)
        → Σ (Fin n) (Γ ⊢_∈ α)
  Σ-/ (i Σ., ⊢i) (ρ Σ., ⊢ρ) = (i / ρ) Σ., (/-preserv ⊢i ⊢ρ)      

  Σ-id : ∀ {n} {Γ : Ctx n} → Σ (Ren n n) (Γ ⊢_∈s Γ)
  Σ-id = id Σ., id-preserv

  Σ-p : ∀ {n α} {Γ : Ctx n} → Σ (Ren (suc n) n) (Γ ⊢_∈s Γ ∙ α)
  Σ-p = p Σ., p-preserv

  Σ-q : ∀ {n α} {Γ : Ctx n} → Σ (Fin (suc n)) (Γ ∙ α ⊢_∈ α)
  Σ-q = zero Σ., ⊢q

  ImpSubScwf : Scwf
  ImpSubScwf = record
                 { ucwf   = ImpSubUcwf
                 ; Ty     = Ty
                 ; Ctx    = Ctx
                 ; ε      = []
                 ; _∙_    = _∙_
                 ; _⊢_∈_  = _⊢_∈_
                 ; _⊢_∈s_ = _⊢_∈s_
                 ; Σ-<>   = Σ-[]
                 ; Σ-<,>  = Σ-,
                 ; Σ-∘    = Σ-∘
                 ; Σ-sub  = Σ-/
                 ; Σ-id   = Σ-id
                 ; Σ-p    = Σ-p
                 ; Σ-q    = Σ-q
                 }
