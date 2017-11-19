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

id=<pq> : ∀ {Γ α} → id {Γ ∙ α} ≡ (q , p)
id=<pq> {ε}     = refl
id=<pq> {Γ ∙ x} = refl

[] : ∀ {Γ} → Γ ▹ ε
[] = tt

⋆-<> : ∀ {Γ Δ} (ρ : Γ ▹ Δ) → [] {Γ} ⋆ ρ ≡ [] {Γ}
⋆-<> _ = refl

q[] : ∀ {Γ Δ α} (t : Term Γ α) (ρ : Γ ▹ Δ) → q [ t , ρ ] ≡ t
q[] t ρ = refl

p⋆, : ∀ {Δ Θ α} (t : Term Δ α) (γ : Δ ▹ Θ) → p ⋆ (t , γ) ≡ γ

idL : ∀ {Γ Δ} (ρ : Δ ▹ Γ) → id ⋆ ρ ≡ ρ

p⋆, {Θ = Θ} t = trans (⋆-step Θ id _ t) ∘ idL

idL {ε}     tt      = refl
idL {Γ ∙ α} (t , ρ) = cong (t ,_) (p⋆, t ρ)

[]-asso : ∀ {Γ Δ Θ α} (t : Term Γ α) (γ : Δ ▹ Γ) (δ : Θ ▹ Δ) →
          t [ γ ⋆ δ ] ≡ t [ γ ] [ δ ]
[]-asso (var here) γ δ = refl
[]-asso (var (there ∈Γ)) (u , γ) δ = []-asso (var ∈Γ) γ δ            
[]-asso (t · u) γ δ = cong₂ _·_ ([]-asso t γ δ) ([]-asso u γ δ)
[]-asso {Γ} {Δ} (ƛ t) γ δ = sym $ cong ƛ $ trans (
     sym ([]-asso t (var here , ▹-weaken Γ (step ⊆-refl) γ)
                    (var here , ▹-weaken Δ (step ⊆-refl) δ)))
     ((cong (t [_] ∘ (var here ,_))
            (trans (⋆-step Γ γ (▹-weaken Δ ⊆-∙ δ) (var here))
                   (wk-⋆ Γ ⊆-∙ γ δ))))

⋆-asso : ∀ {Γ Δ Θ Λ} (γ : Δ ▹ Θ) (δ : Γ ▹ Δ) (ζ : Λ ▹ Γ) →
         (γ ⋆ δ) ⋆ ζ ≡ γ ⋆ (δ ⋆ ζ)
⋆-asso {Θ = ε} tt δ ζ = refl
⋆-asso {Θ = Θ ∙ _} (t , γ) δ ζ =
  trans (cong (_, (γ ⋆ δ) ⋆ ζ) (sym ([]-asso t δ ζ)))
        (cong (t [ δ ⋆ ζ ] ,_) (⋆-asso γ δ ζ))

maps : {Γ Δ : Ctxt Ty} {α : Ty} (t : Term Δ α) (γ : Δ ▹ Γ) (δ : Γ ▹ Δ) →
       ((t [ δ ]) , γ ⋆ δ) ≡ ((t [ δ ]) , γ ⋆ δ)
maps = λ _ _ _ → refl       

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
             ; <_,_>    = flip _,_
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
