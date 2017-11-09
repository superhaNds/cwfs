module SimpTyped.Tm.Context where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

infix 20 _,_

data Ctxt (A : Set) : Set where
  ε   : Ctxt A
  _,_ : Ctxt A → A → Ctxt A

data _⊆_ {A : Set} : Ctxt A → Ctxt A → Set where
  base : ε ⊆ ε
  step : ∀ {Γ Δ : Ctxt A} {σ} (φ : Γ ⊆ Δ) → Γ ⊆ (Δ , σ)
  pop! : ∀ {Γ Δ : Ctxt A} {σ} (ψ : Γ ⊆ Δ) → (Γ , σ) ⊆ (Δ , σ)

⊆-refl : {A : Set} {Γ : Ctxt A} → Γ ⊆ Γ
⊆-refl {Γ = ε} = base 
⊆-refl {Γ = Γ , _} = pop! ⊆-refl

⊆-trans : ∀ {A : Set} {Γ Δ Ε : Ctxt A} → Γ ⊆ Δ → Δ ⊆ Ε → Γ ⊆ Ε
⊆-trans base Δ⊆E = Δ⊆E
⊆-trans (step Γ⊆Δ) (step Δ⊆E) = step (⊆-trans (step Γ⊆Δ) Δ⊆E)
⊆-trans (step Γ⊆Δ) (pop! Δ⊆E) = step (⊆-trans Γ⊆Δ Δ⊆E)
⊆-trans (pop! Γ⊆Δ) (step Δ⊆E) = step (⊆-trans (pop! Γ⊆Δ) Δ⊆E)
⊆-trans (pop! Γ⊆Δ) (pop! Δ⊆E) = pop! (⊆-trans Γ⊆Δ Δ⊆E)

infix 10 _∈_

data _∈_ {A : Set} (a : A) : Ctxt A → Set where
  here  : {Γ : Ctxt A} → a ∈ Γ , a
  there : {Γ : Ctxt A} {x : A} → a ∈ Γ → a ∈ Γ , x

there-eq : {A : Set} {Γ : Ctxt A} {a x : A} {φ ψ : a ∈ Γ} →
           there {x = x} φ ≡ there {x = x} ψ → φ ≡ ψ
there-eq refl = refl           

∈-dec : {A : Set} {Γ : Ctxt A} {a : A} (φ ψ : a ∈ Γ) → Dec (φ ≡ ψ)
∈-dec here here = yes refl
∈-dec here (there ψ) = no (λ ())
∈-dec (there φ) here = no (λ ())
∈-dec (there φ) (there ψ) with ∈-dec φ ψ
∈-dec (there φ) (there _) | yes refl = yes refl
∈-dec (there φ) (there _) | no ¬p = no (λ p → ¬p (there-eq p))
