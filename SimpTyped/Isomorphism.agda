module SimpTyped.Isomorphism where

open import SimpTyped.ScwfComb renaming (Tm to Tm-cwf)
open import SimpTyped.Tm.Syntax renaming (Term to Tm-λ ; q to q~ ; weaken to weaken~ ; _[_] to _[_]' ; p to p~ ; id to id~)
open import SimpTyped.Context
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
