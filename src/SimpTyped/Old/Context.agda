-------------------------------------------------------------------------------
-- Contexts with inclusion and membership
-------------------------------------------------------------------------------
module SimpTyped.Old.Context where

open import Relation.Nullary
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Function using (_$_ ; _∘_)

-------------------------------------------------------------------------------
-- Polymorphic contexts and inclusion relation

infix 20 _∙_

data Ctxt (A : Set) : Set where
  ε   : Ctxt A
  _∙_ : Ctxt A → A → Ctxt A

data _⊆_ {A : Set} : Ctxt A → Ctxt A → Set where
  base : ε ⊆ ε
  step : ∀ {Γ Δ : Ctxt A} {σ} (φ : Γ ⊆ Δ) → Γ ⊆ (Δ ∙ σ)
  pop! : ∀ {Γ Δ : Ctxt A} {σ} (ψ : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ σ)

length : {A : Set} → Ctxt A → ℕ
length ε = 0
length (Γ ∙ x) = 1 + length Γ

⊆-refl : {A : Set} {Γ : Ctxt A} → Γ ⊆ Γ
⊆-refl {Γ = ε}     = base 
⊆-refl {Γ = Γ ∙ _} = pop! ⊆-refl

⊆-trans : {A : Set} {Γ Δ Ε : Ctxt A} → Γ ⊆ Δ → Δ ⊆ Ε → Γ ⊆ Ε
⊆-trans base       Δ⊆E        = Δ⊆E
⊆-trans (step Γ⊆Δ) (step Δ⊆E) = step (⊆-trans (step Γ⊆Δ) Δ⊆E)
⊆-trans (step Γ⊆Δ) (pop! Δ⊆E) = step (⊆-trans Γ⊆Δ Δ⊆E)
⊆-trans (pop! Γ⊆Δ) (step Δ⊆E) = step (⊆-trans (pop! Γ⊆Δ) Δ⊆E)
⊆-trans (pop! Γ⊆Δ) (pop! Δ⊆E) = pop! (⊆-trans Γ⊆Δ Δ⊆E)

⊆-trans-refl : {A : Set} {Γ : Ctxt A} → ⊆-trans {A} {Γ} ⊆-refl ⊆-refl ≡ ⊆-refl
⊆-trans-refl {Γ = ε} = refl
⊆-trans-refl {Γ = Γ ∙ x} = cong pop! ⊆-trans-refl

⊆-∙ : {A : Set} {Γ : Ctxt A} {a : A} → Γ ⊆ (Γ ∙ a)
⊆-∙ = step ⊆-refl

infix 10 _∈_

data _∈_ {A : Set} (α : A) : Ctxt A → Set where
  here  : {Γ : Ctxt A} → α ∈ Γ ∙ α
  there : {Γ : Ctxt A} {α′ : A} → α ∈ Γ → α ∈ Γ ∙ α′

there-eq : {A : Set} {Γ : Ctxt A} {a x : A} {φ ψ : a ∈ Γ} →
           there {α′ = x} φ ≡ there {α′ = x} ψ → φ ≡ ψ
there-eq refl = refl           

mapWith∈ : ∀ {A B : Set}
           (Γ : Ctxt A) → (∀ {x} → x ∈ Γ → B) → Ctxt B
mapWith∈ ε       _ = ε
mapWith∈ (Γ ∙ _) f = mapWith∈ Γ (f ∘ there) ∙ (f here)           

∈-dec : {A : Set} {Γ : Ctxt A} {a : A} (φ ψ : a ∈ Γ) → Dec (φ ≡ ψ)
∈-dec here here      = yes refl
∈-dec here (there ψ) = no (λ ())
∈-dec (there φ) here = no (λ ())
∈-dec (there φ) (there ψ) with ∈-dec φ ψ
∈-dec (there φ) (there _) | yes refl = yes refl
∈-dec (there φ) (there _) | no φ≠ψ    = no (φ≠ψ ∘ there-eq)

sub-in : {A : Set} {Γ Δ : Ctxt A} {a : A} → Γ ⊆ Δ → a ∈ Γ → a ∈ Δ
sub-in base a∈Γ               = a∈Γ
sub-in (step Γ⊆Δ) a∈Γ         = there (sub-in Γ⊆Δ a∈Γ)
sub-in (pop! Γ⊆Δ) here        = here
sub-in (pop! Γ⊆Δ) (there a∈Γ) = there (sub-in Γ⊆Δ a∈Γ)

sub-in-refl : ∀ {A : Set} {Δ : Ctxt A} {a} (φ : a ∈ Δ) → sub-in ⊆-refl φ ≡ φ
sub-in-refl here      = refl
sub-in-refl (there φ) = cong there (sub-in-refl φ)

⊆-refl-l : {A : Set} {Γ Δ : Ctxt A} (φ : Γ ⊆ Δ) → ⊆-trans ⊆-refl φ ≡ φ
⊆-refl-l base                 = refl
⊆-refl-l {Γ = ε}     (step φ) = refl
⊆-refl-l {Γ = Γ ∙ x} (step φ) = cong step (⊆-refl-l φ)
⊆-refl-l (pop! φ)             = cong pop! (⊆-refl-l φ)

⊆-refl-r : {A : Set} {Γ Δ : Ctxt A} (φ : Γ ⊆ Δ) → ⊆-trans φ ⊆-refl ≡ φ
⊆-refl-r base     = refl
⊆-refl-r (step φ) = cong step (⊆-refl-r φ)
⊆-refl-r (pop! φ) = cong pop! (⊆-refl-r φ)

⊆-refl-lr : ∀ {A : Set} {Γ Δ : Ctxt A} (φ : Γ ⊆ Δ) → ⊆-trans φ ⊆-refl ≡ ⊆-trans ⊆-refl φ
⊆-refl-lr φ = trans (⊆-refl-r φ) (sym (⊆-refl-l φ))

⊆-step-l : ∀ {A : Set} {Γ Δ Ε} {σ : A} (φ₁ : Γ ⊆ Δ) (φ₂ : Δ ⊆ Ε) →
           step {σ = σ} (⊆-trans φ₁ φ₂) ≡ ⊆-trans (step φ₁) (pop! φ₂)
⊆-step-l base φ₂ = refl
⊆-step-l (step φ₁) φ₂ = refl
⊆-step-l (pop! φ₁) φ₂ = refl

⊆-step-r : ∀ {A : Set} {Γ Δ Ε} {σ : A} (φ₁ : Γ ⊆ Δ) (φ₂ : Δ ⊆ Ε) →
           step {σ = σ} (⊆-trans φ₁ φ₂) ≡ ⊆-trans φ₁ (step φ₂)
⊆-step-r base φ₂ = refl
⊆-step-r (step φ₁) φ₂ = refl
⊆-step-r (pop! φ₁) φ₂ = refl

⊆-step-refl : ∀ {A : Set} {Γ Δ} {σ : A} (φ : Γ ⊆ Δ) →
              step {σ = σ} (⊆-trans ⊆-refl φ) ≡ ⊆-trans φ ⊆-∙
⊆-step-refl φ = trans (cong step (sym (⊆-refl-lr φ))) (⊆-step-r φ ⊆-refl)

sub-in₂ : {A : Set} {Γ Δ Θ : Ctxt A} {a : A} (φ : Γ ⊆ Δ) (ψ : Δ ⊆ Θ) (ω : a ∈ Γ) →
          sub-in ψ (sub-in φ ω) ≡ sub-in (⊆-trans φ ψ) ω
sub-in₂ base base     ()
sub-in₂ base (step ψ) ω = refl
sub-in₂ (step φ) (step ψ) ω = cong there (sub-in₂ (step φ) ψ ω)
sub-in₂ (step φ) (pop! ψ) ω = cong there (sub-in₂ φ ψ ω)
sub-in₂ (pop! φ) (step ψ) ω = cong there (sub-in₂ (pop! φ) ψ ω)
sub-in₂ (pop! φ) (pop! ψ) here = refl
sub-in₂ (pop! φ) (pop! ψ) (there ω) = cong there (sub-in₂ φ ψ ω)          

sub-in-step : {A : Set} → ∀ {Γ Δ σ} {γ : A} (φ : (Γ ∙ γ) ⊆ Δ) (ψ : σ ∈ Γ) →
              sub-in (⊆-trans ⊆-∙ φ) ψ ≡ sub-in φ (there ψ)
sub-in-step {Γ = ε} φ ()
sub-in-step (step φ) ψ = cong there (sub-in-step φ ψ)
sub-in-step (pop! φ) here = cong there (sym (sub-in₂ (pop! ⊆-refl) φ here))
sub-in-step (pop! φ) (there ψ) =
  cong there (trans (trans (sym (sub-in₂ ⊆-refl φ (there ψ)))
                    (sub-in₂ (step ⊆-refl) φ ψ))
             (sub-in-step φ ψ))              
