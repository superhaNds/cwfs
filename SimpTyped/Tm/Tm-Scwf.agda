-------------------------------------------------------------------------------
-- Proof of Scwf axioms for the concrete typed lambda calculus
-------------------------------------------------------------------------------
module SimpTyped.Tm.Tm-Scwf where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import Function using (_$_ ; _∘_ ; flip)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import SimpTyped.Type
open import SimpTyped.Context
open import SimpTyped.Tm.Syntax
open import SimpTyped.Tm.Properties
open import SimpTyped.Scwf
open P.≡-Reasoning

-------------------------------------------------------------------------------
-- Axiom proofs

id=<pq> : ∀ {Γ α} → id {Γ ∙ α} ≡ (p , q)
id=<pq> = refl

-- a synonym for the terminal object

[] : ∀ {Γ} → Γ ▹ ε
[] = tt

-- terminal object is a left zero

⋆-<> : ∀ {Γ Δ} (ρ : Γ ▹ Δ) → [] {Γ} ⋆ ρ ≡ [] {Γ}
⋆-<> _ = refl

-- q is the second projection

q[] : ∀ {Γ Δ α} (t : Term Γ α) (ρ : Γ ▹ Δ) → q [ ρ , t ] ≡ t
q[] t ρ = refl

-- p is the first projection

p⋆, : ∀ {Δ Θ α} (t : Term Δ α) (γ : Δ ▹ Θ) → p ⋆ (γ , t) ≡ γ

-- id is a left identity in composition

idL : ∀ {Γ Δ} (ρ : Δ ▹ Γ) → id ⋆ ρ ≡ ρ

p⋆, {Θ = Θ} t = trans (⋆-step Θ id _ t) ∘ idL

idL {ε}     tt      = refl
idL {Γ ∙ α} (ρ , t) = cong (_, t) (p⋆, t ρ)

-- associativity of substitution

[]-asso : ∀ {Γ Δ Θ α} (t : Term Γ α) (γ : Δ ▹ Γ) (δ : Θ ▹ Δ) →
          t [ γ ⋆ δ ] ≡ t [ γ ] [ δ ]
[]-asso (var here) γ δ = refl
[]-asso (var (there ∈Γ)) (γ , u) δ = []-asso (var ∈Γ) γ δ            
[]-asso (t · u) γ δ = cong₂ _·_ ([]-asso t γ δ) ([]-asso u γ δ)
[]-asso {Γ} {Δ} (ƛ t) γ δ = sym $ cong ƛ $ trans (
     sym ([]-asso t (▹-weaken Γ (step ⊆-refl) γ , var here)
                    (▹-weaken Δ (step ⊆-refl) δ , var here)))
     ((cong (t [_] ∘ (_, var here))
            (trans (⋆-step Γ γ (▹-weaken Δ ⊆-∙ δ) (var here))
                   (wk-⋆ Γ ⊆-∙ γ δ))))

-- associativity of composition

⋆-asso : ∀ {Γ Δ Θ Λ} (γ : Δ ▹ Θ) (δ : Γ ▹ Δ) (ζ : Λ ▹ Γ) →
         (γ ⋆ δ) ⋆ ζ ≡ γ ⋆ (δ ⋆ ζ)
⋆-asso {Θ = ε}     tt      δ ζ = refl
⋆-asso {Θ = Θ ∙ _} (γ , t) δ ζ =
  trans (cong ((γ ⋆ δ) ⋆ ζ ,_) (sym ([]-asso t δ ζ)))
        (cong (_, t [ δ ⋆ ζ ]) (⋆-asso γ δ ζ))

-- composition on the right maps to cons

maps : ∀ {Γ Δ} {α : Ty} (t : Term Δ α) (γ : Δ ▹ Γ) (δ : Γ ▹ Δ) →
        (γ , t) ⋆ δ ≡ (γ ⋆ δ , (t [ δ ]))
maps = λ _ _ _ → refl       

-- scwf record instantiation

TermScwf : Scwf
TermScwf = record
             { Ty       = Ty
             ; Ctx      = Ctx
             ; _,_      = _∙_
             ; ε        = ε
             ; Tm       = Term
             ; Hom      = _▹_
             ; _~_      = _≡_
             ; _~~_     = _≡_
             ; <>       = tt
             ; id       = id
             ; p        = p
             ; q        = q 
             ; _∘_      = _⋆_
             ; _[_]     = _[_]
             ; <_,_>    = _,_
             ; id₀      = idε<>
             ; ∘<>      = ⋆-<>
             ; varp     = id=<pq>
             ; idL      = idL
             ; idR      = idR
             ; assoc    = ⋆-asso
             ; tmId     = t[id]
             ; pCons    = p⋆,
             ; q[]      = q[]
             ; clos     = []-asso
             ; maps     = maps
             ; cong-[]  = cong-[]
             ; cong-<,> = cong-,
             ; cong-∘   = cong-⋆
             }

-- here we use the fact that γ ⋆ p is the same as weakening γ

lamCm : ∀ {Γ Δ} {α β} (t : Term (Γ ∙ α) β) (γ : Δ ▹ Γ) →
         ƛ (t [ ▹-weaken Γ (step ⊆-refl) γ , var here ]) ≡ ƛ (t [ γ ⋆ p , var here ])
lamCm {α = α} t γ rewrite sym (▹-weaken-⋆-p {α = α} γ)= refl        

TermLamScwf : Lambda-scwf
TermLamScwf = record
                { scwf   = TermScwf
                ; _`→_   = _⇒_
                ; ƛ      = ƛ
                ; _·_    = _·_
                ; appCm  = λ _ _ _ → refl
                ; lamCm  = lamCm
                ; cong-ƛ = ƛ-eq
                ; cong-· = app-eq
                }
