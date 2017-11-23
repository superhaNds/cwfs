module SimpTyped.Isomorphism where

open import SimpTyped.ScwfComb renaming (Tm to Tm-cwf)
open import SimpTyped.Tm.Syntax
  renaming (Term to Tm-λ ; q to q~ ; weaken to weaken~ ; _[_] to _[_]'
  ; p to p~ ; id to id~ ; cong-[] to cong-[]')
open import SimpTyped.Context
open import SimpTyped.Tm.Properties
open import SimpTyped.Context
open import SimpTyped.Type
open import Function using (_$_ ; flip)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_] ; cong-app)
open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)

⟦_⟧  : ∀ {Γ α} → Tm-λ Γ α → Tm-cwf Γ α
⟪_⟫  : ∀ {Γ α} → Tm-cwf Γ α → Tm-λ Γ α
⟪_⟫ʰ : ∀ {Γ Δ} → Hom Δ Γ → Δ ▹ Γ
⟦_⟧ˢ : ∀ {Γ Δ} → Δ ▹ Γ → Hom Δ Γ

⟦ var ∈Γ ⟧  = varCwf ∈Γ
⟦ t · u ⟧   = app ⟦ t ⟧ ⟦ u ⟧
⟦ ƛ t ⟧     = lam ⟦ t ⟧

⟪ q ⟫       = var here
⟪ t [ ρ ] ⟫ = ⟪ t ⟫ [ ⟪ ρ ⟫ʰ ]'
⟪ lam t ⟫   = ƛ ⟪ t ⟫
⟪ app t u ⟫ = ⟪ t ⟫ · ⟪ u ⟫

⟦_⟧ˢ {ε}     _       = <>
⟦_⟧ˢ {Γ ∙ α} (t , ρ) = < ⟦ ρ ⟧ˢ , ⟦ t ⟧ >

⟪ <> ⟫ʰ        = tt
⟪ id ⟫ʰ        = id~
⟪ p  ⟫ʰ        = p~
⟪ γ ∘ γ' ⟫ʰ    = ⟪ γ ⟫ʰ ⋆ ⟪ γ' ⟫ʰ
⟪ < γ , t > ⟫ʰ = ⟪ t ⟫ , ⟪ γ ⟫ʰ

hom∘▹ : ∀ {Γ Δ} (γ : Hom Γ Δ) → ⟦ ⟪ γ ⟫ʰ ⟧ˢ ~~ γ

λ∘cwf : ∀ {Γ α} (t : Tm-λ Γ α) → ⟪ ⟦ t ⟧ ⟫ ≡ t

cwf∘λ : ∀ {Γ α} (t : Tm-cwf Γ α) → ⟦ ⟪ t ⟫ ⟧ ~ t

[]-comm : ∀ {Γ Δ α} (t : Tm-λ Γ α) (ρ : Δ ▹ Γ) →
          ⟦ t [ ρ ]' ⟧ ~ ⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]
          
⟦⟧-∘-dist : ∀ {Γ Δ Θ} (ρ : Δ ▹ Θ) (σ : Γ ▹ Δ) →
            ⟦ ρ ⋆ σ ⟧ˢ ~~ ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ

postulate ⟦⟧-∘-distₚ : ∀ {Γ Δ Θ} (ρ : Δ ▹ Θ) (σ : Γ ▹ Δ) → ⟦ ρ ⋆ σ ⟧ˢ ~~ ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ

[]-comm {ε} (var ()) tt
[]-comm (var here) (t , ρ) = sym~ (q[] ⟦ t ⟧ ⟦ ρ ⟧ˢ)
[]-comm (var (there ∈Γ)) (t , ρ) = begin
  ⟦ tkVar ∈Γ ρ ⟧
    ≈⟨ []-comm (var ∈Γ) ρ ⟩
  ⟦ var ∈Γ ⟧ [ ⟦ ρ ⟧ˢ ]
    ≈⟨ cong-[] refl~ (sym~~ (pCons ⟦ t ⟧ ⟦ ρ ⟧ˢ)) ⟩
  ⟦ var ∈Γ ⟧ [ p ∘ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ]
    ≈⟨ clos ⟦ var ∈Γ ⟧ p < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ⟩
  ⟦ var ∈Γ ⟧ [ p ] [ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ]
    ∎
  where open EqR (TmCwf {_})
[]-comm (t · u) ρ = begin
  app ⟦ t [ ρ ]' ⟧ ⟦ u [ ρ ]' ⟧
    ≈⟨ cong-app ([]-comm t ρ) refl~ ⟩
  app (⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]) ⟦ u [ ρ ]' ⟧
    ≈⟨ cong-app refl~ ([]-comm u ρ) ⟩
  app (⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]) (⟦ u ⟧ [ ⟦ ρ ⟧ˢ ])
    ≈⟨ appCm ⟦ t ⟧ ⟦ u ⟧ ⟦ ρ ⟧ˢ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ [ ⟦ ρ ⟧ˢ ]
    ∎
  where open EqR (TmCwf {_})
[]-comm {Γ} (ƛ {α = γ} t) ρ = begin
  lam ⟦ t [ var here , ▹-weaken Γ ⊆-∙ ρ ]' ⟧
    ≈⟨ cong-lam ([]-comm t (var here , ▹-weaken Γ ⊆-∙ ρ)) ⟩
  lam (⟦ t ⟧ [ < ⟦ ▹-weaken Γ ⊆-∙ ρ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-[] refl~ (help)) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⋆ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-[] refl~ (cong-<,> refl~ (⟦⟧-∘-distₚ ρ p~))) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⟧ˢ ∘ ⟦ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-[] refl~ (cong-<,> refl~ (cong-∘ refl~~ {!!}))) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⟧ˢ ∘ p , q > ])
    ≈⟨ sym~ (lamCm ⟦ t ⟧ ⟦ ρ ⟧ˢ) ⟩
  lam ⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]
    ∎
  where open EqR (TmCwf {_})
        help : < ⟦ ▹-weaken Γ (⊆-∙ {a = γ}) ρ ⟧ˢ , q > ~~ < ⟦ ρ ⋆ p~ ⟧ˢ , q >
        help rewrite ▹-weaken-⋆-p {Γ} {α = γ} ρ = refl~~
  
⟦⟧-∘-dist {Θ = ε} tt σ = sym~~ (∘<> ⟦ σ ⟧ˢ)
⟦⟧-∘-dist {Θ = Θ ∙ x} (t , ρ) σ = begin
  < ⟦ ρ ⋆ σ ⟧ˢ , ⟦ t [ σ ]' ⟧ >
    ≈⟨ cong-<,> refl~ (⟦⟧-∘-dist ρ σ) ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t [ σ ]' ⟧ >
    ≈⟨ cong-<,> ([]-comm t σ) refl~~ ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t ⟧ [ ⟦ σ ⟧ˢ ] >
    ≈⟨ sym~~ (maps ⟦ t ⟧ ⟦ ρ ⟧ˢ ⟦ σ ⟧ˢ) ⟩
  < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ∘ ⟦ σ ⟧ˢ
    ∎
  where open EqR (HmSetoid {_} {_})

λ∘cwf (var here) = refl
λ∘cwf (t · u) = cong₂ _·_ (λ∘cwf t) (λ∘cwf u)
λ∘cwf (ƛ t) = cong ƛ (λ∘cwf t)
λ∘cwf {α = α} (var (there ∈Γ)) = begin
  ⟪ ⟦ var ∈Γ ⟧ ⟫ [ p~ ]'
    ≡⟨ cong (_[ p~ ]') (λ∘cwf (var ∈Γ)) ⟩
  var ∈Γ [ p~ ]'
    ≡⟨ sub-p (var ∈Γ) ⟩
  weaken~ ⊆-∙ (var ∈Γ)
    ≡⟨⟩
  var (there (sub-in ⊆-refl ∈Γ))
    ≡⟨ cong (λ x → var (there x)) (sub-in-refl ∈Γ) ⟩
  var (there ∈Γ)
    ∎
  where open P.≡-Reasoning

cwf∘λ q = refl~
cwf∘λ (lam t) = cong-lam (cwf∘λ t)
cwf∘λ (app t u) = cong-app (cwf∘λ t) (cwf∘λ u)
cwf∘λ (t [ γ ]) = begin
  ⟦ ⟪ t ⟫ [ ⟪ γ ⟫ʰ ]' ⟧
    ≈⟨ []-comm ⟪ t ⟫ ⟪ γ ⟫ʰ ⟩
  ⟦ ⟪ t ⟫ ⟧ [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ]
    ≈⟨ cong-[] (cwf∘λ t) refl~~ ⟩
  t [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ]
    ≈⟨ cong-[] refl~ (hom∘▹ γ) ⟩
  t [ γ ]
    ∎
  where open EqR (TmCwf {_})

hom∘▹ <> = refl~~
hom∘▹ (id {ε}) = sym~~ (homε~<> id)
hom∘▹ (id {Γ ∙ α}) = sym~~ $ begin
  id               ≈⟨ varp ⟩
  < p , q >        ≈⟨ cong-<,> refl~ (sym~~ (hom∘▹ p)) ⟩
  < ⟦ p~ ⟧ˢ , q >  ∎
  where open EqR (HmSetoid {_} {_})
hom∘▹ (p {ε}) = sym~~ (homε~<> p)
hom∘▹ (p {Δ ∙ x}) = {!!}
hom∘▹ (γ ∘ γ') = begin
  ⟦ ⟪ γ ⟫ʰ ⋆ ⟪ γ' ⟫ʰ ⟧ˢ      ≈⟨ ⟦⟧-∘-dist ⟪ γ ⟫ʰ ⟪ γ' ⟫ʰ ⟩
  ⟦ ⟪ γ ⟫ʰ ⟧ˢ ∘ ⟦ ⟪ γ' ⟫ʰ ⟧ˢ ≈⟨ cong-∘ (hom∘▹ γ) refl~~ ⟩
  γ ∘ ⟦ ⟪ γ' ⟫ʰ ⟧ˢ           ≈⟨ cong-∘ refl~~ (hom∘▹ γ') ⟩
  γ ∘ γ'                     ∎
  where open EqR (HmSetoid {_} {_})
hom∘▹ < γ , α > = begin
  < ⟦ ⟪ γ ⟫ʰ ⟧ˢ , ⟦ ⟪ α ⟫ ⟧ > ≈⟨ cong-<,> refl~ (hom∘▹ γ) ⟩
  < γ , ⟦ ⟪ α ⟫ ⟧ >           ≈⟨ cong-<,> (cwf∘λ α) refl~~ ⟩
  < γ , α >                   ∎
  where open EqR (HmSetoid {_} {_})
