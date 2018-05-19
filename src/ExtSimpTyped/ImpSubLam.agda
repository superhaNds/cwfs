module ExtSimpTyped.ImpSubLam where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec hiding ([_])
open import Data.Fin
open import Data.Product using (Σ)
open import Unityped.ImpSubLam
open import Unityped.ImpSub as Ren using (Ren)

infixr 20 _⇒_

data Ty : Set where
  ♭   : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Nat → Set
Ctx = Vec Ty

_∙_ : ∀ {n} (Γ : Ctx n) (α : Ty) → Ctx (suc n)
Γ ∙ α = α ∷ Γ

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctx n) : Tm n → Ty → Set where
  ⊢var : ∀ {i} →  Γ ⊢ var i ∈ lookup i Γ
  
  ⊢ƛ : ∀ {t α β}
       → Γ ∙ α ⊢ t ∈ β
       → Γ ⊢ ƛ t ∈ α ⇒ β
              
  ⊢app : ∀ {t u σ τ}
         → Γ ⊢ t ∈ σ ⇒ τ
         → Γ ⊢ u ∈ σ
         → Γ ⊢ app t u ∈ τ

⊢q : ∀ {n α} {Γ : Ctx n} → Γ ∙ α ⊢ q ∈ α
⊢q = ⊢var

infix 4 _⊢_∈s_

data _⊢_∈s_ : ∀ {n m} → Ctx n → Sub m n → Ctx m → Set where
  ⊢[] : ∀ {m} {Δ : Ctx m} → [] ⊢ [] ∈s Δ
  
  ⊢,  : ∀ {m n} {Γ Δ α} {σ : Sub m n} {t : Tm m}
        → Γ ⊢ σ ∈s Δ
        → Δ ⊢ t ∈ α
        → Γ ∙ α ⊢ σ , t ∈s Δ

module Var where

  map-suc-preserv : ∀ {m n α Γ Δ} (ρ : Ren m n)
                    → Γ ⊢ map var ρ ∈s Δ
                    → Γ ⊢ map var (map suc ρ) ∈s Δ ∙ α
  map-suc-preserv []      ⊢[]          = ⊢[]
  map-suc-preserv (x ∷ ρ) (⊢, ⊢ρ ⊢var) = ⊢, (map-suc-preserv ρ ⊢ρ) ⊢var

  ↑-preserv : ∀ {m n α Γ Δ} {ρ : Ren m n}
              → Γ ⊢ map var ρ ∈s Δ
              → Γ ∙ α ⊢ map var (Ren.↑ ρ) ∈s Δ ∙ α
  ↑-preserv {ρ = ρ} ⊢ρ = ⊢, (map-suc-preserv ρ ⊢ρ) ⊢var

  id-preserv : ∀ {n} {Γ : Ctx n}
               → Γ ⊢ map var (Ren.id) ∈s Γ
  id-preserv {Γ = []}    = ⊢[]
  id-preserv {Γ = _ ∷ _} = ↑-preserv id-preserv               

  p-preserv : ∀ {n α} {Γ : Ctx n} → Γ ⊢ p ∈s (Γ ∙ α)
  p-preserv = map-suc-preserv Ren.id id-preserv

  lookup-preserv : ∀ {m n Γ Δ} i (ρ : Ren m n)
                 → Γ ⊢ map var ρ ∈s Δ
                 → Δ ⊢ var (lookup i ρ) ∈ lookup i Γ
  lookup-preserv zero    (_ ∷ _) (⊢, _ ∈α) = ∈α
  lookup-preserv (suc i) (_ ∷ ρ) (⊢, ⊢ρ _) = lookup-preserv i ρ ⊢ρ

  /-preserv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {t ρ α}
              → Γ ⊢ t ∈ α
              → Γ ⊢ map var ρ ∈s Δ
              → Δ ⊢ t / ρ ∈ α
  /-preserv (⊢var {i})   ⊢ρ = lookup-preserv i _ ⊢ρ
  /-preserv (⊢ƛ ⊢t)      ⊢ρ = ⊢ƛ (/-preserv ⊢t (↑-preserv ⊢ρ))
  /-preserv (⊢app ⊢t ⊢u) ⊢ρ = ⊢app (/-preserv ⊢t ⊢ρ) (/-preserv ⊢u ⊢ρ)

weaken-preserv : ∀ {n α β Γ} {t : Tm n}
                 → Γ ⊢ t ∈ α
                 → Γ ∙ β ⊢ weaken t ∈ α
weaken-preserv ⊢t = Var./-preserv ⊢t Var.p-preserv                

map-weaken-preserv : ∀ {m n α Γ Δ} {σ : Sub m n}
                     → Γ ⊢ σ ∈s Δ
                     → Γ ⊢ map weaken σ ∈s Δ ∙ α
map-weaken-preserv ⊢[]        = ⊢[]
map-weaken-preserv (⊢, ⊢σ ⊢t) = ⊢, (map-weaken-preserv ⊢σ) (weaken-preserv ⊢t)

↑-preserv : ∀ {m n Γ Δ α} {σ : Sub m n}
            → Γ ⊢ σ ∈s Δ
            → Γ ∙ α ⊢ ↑ σ ∈s Δ ∙ α
↑-preserv ⊢σ = ⊢, (map-weaken-preserv ⊢σ) ⊢var            

id-preserv : ∀ {n} {Γ : Ctx n} → Γ ⊢ id ∈s Γ
id-preserv = Var.id-preserv

p-preserv : ∀ {n α} {Γ : Ctx n} → Γ ⊢ p ∈s Γ ∙ α
p-preserv = Var.p-preserv

lookup-preserv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} i {σ}
                 → Γ ⊢ σ ∈s Δ
                 → Δ ⊢ lookup i σ ∈ lookup i Γ
lookup-preserv zero    (⊢, _ ⊢t) = ⊢t
lookup-preserv (suc i) (⊢, ⊢σ _) = lookup-preserv i ⊢σ                 

sub-preserves : ∀ {m n α t Γ Δ} {σ : Sub m n}
                → Γ ⊢ t ∈ α
                → Γ ⊢ σ ∈s Δ
                → Δ ⊢ t [ σ ] ∈ α
sub-preserves (⊢var {i})   ⊢σ = lookup-preserv i ⊢σ
sub-preserves (⊢ƛ ⊢t)      ⊢σ = ⊢ƛ (sub-preserves ⊢t (↑-preserv ⊢σ))
sub-preserves (⊢app ⊢t ⊢u) ⊢σ = ⊢app (sub-preserves ⊢t ⊢σ) (sub-preserves ⊢u ⊢σ)                

∘-preserv : ∀ {m n k} {Γ Δ Θ} {ρ : Sub m n} {σ : Sub k m}
            → Θ ⊢ ρ ∈s Δ
            → Δ ⊢ σ ∈s Γ
            → Θ ⊢ ρ ∘ σ ∈s Γ
∘-preserv ⊢[]        ⊢σ = ⊢[]
∘-preserv (⊢, ⊢ρ ⊢t) ⊢σ = ⊢, (∘-preserv ⊢ρ ⊢σ) (sub-preserves ⊢t ⊢σ)

private

  Σ-[] : ∀ {m} {Δ : Ctx m} → Σ (Sub m 0) ([] ⊢_∈s Δ)
  Σ-[] = [] Σ., ⊢[]

  Σ-, : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
        → Σ (Sub m n) (Γ ⊢_∈s Δ)
        → Σ (Tm m) (Δ ⊢_∈ α)
        → Σ (Sub m (suc n)) (Γ ∙ α ⊢_∈s Δ)
  Σ-, (ρ Σ., ⊢ρ) (t Σ., ⊢t) = ρ , t Σ., ⊢, ⊢ρ ⊢t      

  Σ-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
        → Σ (Sub m n) (Γ ⊢_∈s Δ)
        → Σ (Sub k m) (Δ ⊢_∈s Θ)
        → Σ (Sub k n) (Γ ⊢_∈s Θ)
  Σ-∘ (ρ Σ., ⊢ρ) (σ Σ., ⊢σ) = (ρ ∘ σ) Σ., (∘-preserv ⊢ρ ⊢σ)      

  Σ-sub : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
        → Σ (Tm m) (Δ ⊢_∈ α)
        → Σ (Sub n m) (Δ ⊢_∈s Γ)
        → Σ (Tm n) (Γ ⊢_∈ α)
  Σ-sub (t Σ., ⊢t) (ρ Σ., ⊢ρ) = (t [ ρ ]) Σ., (sub-preserves ⊢t ⊢ρ)      

  Σ-id : ∀ {n} {Γ : Ctx n} → Σ (Sub n n) (Γ ⊢_∈s Γ)
  Σ-id = id Σ., id-preserv

  Σ-p : ∀ {n α} {Γ : Ctx n} → Σ (Sub (suc n) n) (Γ ⊢_∈s Γ ∙ α)
  Σ-p = p Σ., p-preserv

  Σ-q : ∀ {n α} {Γ : Ctx n} → Σ (Tm (suc n)) (Γ ∙ α ⊢_∈ α)
  Σ-q = q Σ., ⊢q

  Σ-ƛ : ∀ {n} {Γ : Ctx n} {α β}
        → Σ (Tm (suc n)) (Γ ∙ α ⊢_∈ β)
        → Σ (Tm n) (Γ ⊢_∈ (α ⇒ β))
  Σ-ƛ (t Σ., ⊢t) = ƛ t Σ., ⊢ƛ ⊢t  

  Σ-app : ∀ {n} {Γ : Ctx n} {α β}
          → Σ (Tm n) (Γ ⊢_∈ (α ⇒ β))
          → Σ (Tm n) (Γ ⊢_∈ α)
          → Σ (Tm n) (Γ ⊢_∈ β)
  Σ-app (t Σ., ⊢t) (u Σ., ⊢u) = (app t u) Σ., (⊢app ⊢t ⊢u)
