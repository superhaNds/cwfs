module SimpTyped.Isomorphism where

open import SimpTyped.ScwfComb renaming (Tm to Tm-cwf)
open import SimpTyped.Tm.Syntax
  renaming (Term to Tm-λ ; q to q~ ; weaken to weaken~ ; _[_] to _[_]'
  ; p to p~ ; id to id~ ; _~_ to _~β_ ; refl~ to refl~β ; sym~ to sym~β ; trans~ to trans~β ; cong-[] to cong-[]')
open import SimpTyped.Context
open import SimpTyped.Tm.Properties renaming (maps to maps~ ; q[] to q[]~)
open import SimpTyped.Context
open import Function using (_$_ ; flip)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)


⟦_⟧  : ∀ {Γ α} → Tm-λ Γ α → Tm-cwf Γ α
⟪_⟫  : ∀ {Γ α} → Tm-cwf Γ α → Tm-λ Γ α
⟪_⟫ʰ : ∀ {Γ Δ} → Hom Δ Γ → Δ ▹ Γ
⟦_⟧ˢ : ∀ {Γ Δ} → Δ ▹ Γ → Hom Δ Γ

⟦ var here ⟧       = q
⟦ var (there ∈Γ) ⟧ = ⟦ var ∈Γ ⟧ [ p ]

⟪ q ⟫       = var here
⟪ t [ ρ ] ⟫ = ⟪ t ⟫ [ ⟪ ρ ⟫ʰ ]'

⟦_⟧ˢ {ε}     _       = <>
⟦_⟧ˢ {Γ ∙ α} (t , ρ) = < ⟦ ρ ⟧ˢ , ⟦ t ⟧ >

⟪ <> ⟫ʰ        = tt 
⟪ id ⟫ʰ        = id~
⟪ p ⟫ʰ         = p~
⟪ γ ∘ γ' ⟫ʰ    = ⟪ γ ⟫ʰ ⋆ ⟪ γ' ⟫ʰ
⟪ < γ , t > ⟫ʰ = ⟪ t ⟫ , ⟪ γ ⟫ʰ

hom∘▹ : ∀ {Γ Δ} (γ : Hom Γ Δ) → ⟦ ⟪ γ ⟫ʰ ⟧ˢ ~~ γ
λ∘cwf : ∀ {Γ α} (t : Tm-λ Γ α) → ⟪ ⟦ t ⟧ ⟫ ~β t
cwf∘λ : ∀ {Γ α} (t : Tm-cwf Γ α) → ⟦ ⟪ t ⟫ ⟧ ~ t

[]-comm : ∀ {Γ Δ α} (t : Tm-λ Γ α) (ρ : Δ ▹ Γ) → ⟦ t [ ρ ]' ⟧ ~ ⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]
⟦⟧-∘-dist : ∀ {Γ Δ Θ} (ρ : Δ ▹ Θ) (σ : Γ ▹ Δ) → ⟦ ρ ⋆ σ ⟧ˢ ~~ ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ

[]-comm {ε} (var ()) tt
[]-comm (var here) (t , ρ) = sym~ (q[] ⟦ t ⟧ ⟦ ρ ⟧ˢ)
[]-comm (var (there ∈Γ)) (t , ρ) = begin
  ⟦ tkVar ∈Γ ρ ⟧                          ≈⟨ []-comm (var ∈Γ) ρ ⟩
  ⟦ var ∈Γ ⟧ [ ⟦ ρ ⟧ˢ ]                   ≈⟨ cong-[] refl~ (sym~~ (pCons ⟦ t ⟧ ⟦ ρ ⟧ˢ)) ⟩
  ⟦ var ∈Γ ⟧ [ p ∘ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ]   ≈⟨ clos ⟦ var ∈Γ ⟧ p < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ⟩
  ⟦ var ∈Γ ⟧ [ p ] [ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ] ∎
  where open EqR (TmCwf {_})

⟦⟧-∘-dist {Θ = ε} tt σ = sym~~ (∘<> ⟦ σ ⟧ˢ)
⟦⟧-∘-dist {Θ = Θ ∙ x} (t , ρ) σ = begin
  < ⟦ ρ ⋆ σ ⟧ˢ , ⟦ t [ σ ]' ⟧ >          ≈⟨ cong-<,> refl~ (⟦⟧-∘-dist ρ σ) ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t [ σ ]' ⟧ >     ≈⟨ cong-<,> ([]-comm t σ) refl~~ ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t ⟧ [ ⟦ σ ⟧ˢ ] > ≈⟨ sym~~ (maps ⟦ t ⟧ ⟦ ρ ⟧ˢ ⟦ σ ⟧ˢ) ⟩
  < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ∘ ⟦ σ ⟧ˢ            ∎
  where open EqR (HmSetoid {_} {_})

λ∘cwf (var here)       = refl~β
λ∘cwf {α = α} (var (there ∈Γ)) = begin
  ⟪ ⟦ var ∈Γ ⟧ ⟫ [ p~ ]'         ≈⟨ cong-[]' (λ∘cwf (var ∈Γ)) refl ⟩
  (var ∈Γ) [ p~ ]'               ≈⟨ subst≡ (sub-p (var ∈Γ)) ⟩
  weaken~ ⊆-∙ (var ∈Γ)           ≈⟨ refl~β ⟩
  var (there (sub-in ⊆-refl ∈Γ)) ≈⟨ cong≡~ (λ x → var (there x)) (sub-in-refl ∈Γ) ⟩
  var (there ∈Γ)                 ∎
  where open EqR (Tm~β {_} {_})

cwf∘λ q = refl~
cwf∘λ (t [ γ ]) = begin
  ⟦ ⟪ t ⟫ [ ⟪ γ ⟫ʰ ]' ⟧     ≈⟨ []-comm ⟪ t ⟫ ⟪ γ ⟫ʰ ⟩
  ⟦ ⟪ t ⟫ ⟧ [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ] ≈⟨ cong-[] (cwf∘λ t) refl~~ ⟩
  t [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ]         ≈⟨ cong-[] refl~ (hom∘▹ γ) ⟩
  t [ γ ]                   ∎
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
