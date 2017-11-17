---------------------------------------------------------------------------------------------------
-- Contains the definitions of the bijections between the setoids of wellscoped terms and terms as
-- a Ucwf. Moreover, a proof that they are inverses of each other, which means the objects
-- are isomorphic in the category of cwfs.
---------------------------------------------------------------------------------------------------

module Unityped.Isomorphism where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_$_ ; flip)
open import Unityped.UcwfModel renaming (Term to Tm-cwf ; _[_] to _`[_])
open import Unityped.Wellscoped
  renaming (Term to Tm-λ ; p to p~ ; p′ to p′~ ; id to id~ ; weakenₛ to weaken~ ; q to q~ ; congSub to cong-[]λ)
  hiding (maps)
open import Unityped.Projection renaming (var to varPr)
open import Unityped.Wellscoped.Properties  
open import Relation.Binary.PropositionalEquality hiding ([_] ; cong-app)
import Relation.Binary.EqReasoning as EqR

---------------------------------------------------------------------------------------------------
-- The bijection between wellscoped λ terms and terms as a Ucwf

-- The translation functions (morphisms)

⟦_⟧  : ∀ {n} → Tm-λ n → Tm-cwf n
⟦_⟧ˢ : ∀ {m n} → Subst m n → Hom m n
⟪_⟫  : ∀ {n} → Tm-cwf n → Tm-λ n
⟪_⟫ʰ : ∀ {m n} → Hom m n → Subst m n

-- Substitutions as vectors to a Hom

⟦ [] ⟧ˢ    = <>
⟦ t ∷ σ ⟧ˢ = < ⟦ σ ⟧ˢ , ⟦ t ⟧ > 

-- Traditional lambda calculus terms to Ucwf terms

⟦ var i ⟧ = varPr i
⟦ ƛ t ⟧   = lam ⟦ t ⟧
⟦ t · u ⟧ = app ⟦ t ⟧ ⟦ u ⟧

-- Ucwf terms to lambda terms, (substitution is a constructor which is mapped to the meta operation)

⟪ q ⟫         = var zero
⟪ t `[ us ] ⟫ = ⟪ t ⟫ [ ⟪ us ⟫ʰ ]
⟪ lam t ⟫     = ƛ ⟪ t ⟫
⟪ app t u ⟫   = ⟪ t ⟫ · ⟪ u ⟫

-- Homs to vector substitutions

⟪ id ⟫ʰ         = id~
⟪ ts ∘ us ⟫ʰ    = ⟪ ts ⟫ʰ ⋆ ⟪ us ⟫ʰ
⟪ p ⟫ʰ          = p~
⟪ <> ⟫ʰ         = []
⟪ < ts , t > ⟫ʰ = ⟪ ts ⟫ʰ ∙ ⟪ t ⟫

---------------------------------------------------------------------------------------------------
-- Proofs that the translation functions are inverses of each other

-- Auxiliary props

lemmaₚ : ∀ n → pNorm n ~ₕ ⟦ p~ ⟧ˢ
  
p~⟦p⟧ : ∀ {n} → p ~ₕ ⟦ p~ ⟧ˢ
p~⟦p⟧ {n} = sym~ₕ $ trans~ₕ (sym~ₕ $ lemmaₚ n) (sym~ₕ (p~vars n))

-- Interpreting a composition distributes

postulate ⟦⟧-∘-distₚ : ∀ {m n k} (σ : Subst n k) (γ : Subst m n) → ⟦ σ ⋆ γ ⟧ˢ ~ₕ ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ

⟦⟧-∘-dist : ∀ {m n k} (σ : Subst n k) (γ : Subst m n) → ⟦ σ ⋆ γ ⟧ˢ ~ₕ ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ

-- Interpreting a substitution commutes

[]-comm : ∀ {m n} (t : Tm-λ n) (σ : Subst m n) → ⟦ t [ σ ] ⟧ ~ₜ ⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]

[]-comm (var zero)    (x ∷ σ) = qCons ⟦ x ⟧ ⟦ σ ⟧ˢ
[]-comm (var (suc ι)) (x ∷ σ) = sym~ₜ $ begin
  ⟦ var ι ⟧ `[ p ] `[ < ⟦ σ ⟧ˢ , ⟦ x ⟧ > ]
    ≈⟨ sym~ₜ (clos ⟦ var ι ⟧ p < ⟦ σ ⟧ˢ , ⟦ x ⟧ >) ⟩
  ⟦ var ι ⟧ `[ p ∘ < ⟦ σ ⟧ˢ , ⟦ x ⟧ > ]
    ≈⟨ sym~ₜ (cong-[] refl~ₜ (pCons ⟦ x ⟧ ⟦ σ ⟧ˢ)) ⟩
  ⟦ var ι ⟧ `[ ⟦ σ ⟧ˢ ]
    ≈⟨ sym~ₜ ([]-comm (var ι) σ) ⟩
  ⟦ lookup ι σ ⟧
    ∎
  where open EqR (TermS {_})

[]-comm (t · u) σ = begin
  app ⟦ t [ σ ] ⟧ ⟦ u [ σ ] ⟧
    ≈⟨ cong-app ([]-comm t σ) refl~ₜ ⟩
  app (⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]) (⟦ u [ σ ] ⟧)
    ≈⟨ cong-app refl~ₜ ([]-comm u σ) ⟩
  app (⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]) (⟦ u ⟧ `[ ⟦ σ ⟧ˢ ])
    ≈⟨ appCm ⟦ t ⟧ ⟦ u ⟧ ⟦ σ ⟧ˢ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ `[ ⟦ σ ⟧ˢ ]
    ∎
  where open EqR (TermS {_})

[]-comm (ƛ t) σ = begin
  lam ⟦ t [ ↑ₛ σ ] ⟧
    ≈⟨ cong-lam $ []-comm t (↑ₛ σ) ⟩
  lam (⟦ t ⟧ `[ < ⟦ map weaken~ σ ⟧ˢ , q > ])
    ≈⟨ cong-lam $ cong-[] refl~ₜ help ⟩
  lam (⟦ t ⟧ `[ < ⟦ σ ⋆ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam $ cong-[] refl~ₜ (cong-<,> refl~ₜ (⟦⟧-∘-distₚ σ p~)) ⟩ 
  lam (⟦ t ⟧ `[ < ⟦ σ ⟧ˢ ∘ ⟦ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam $ cong-[] refl~ₜ (cong-<,> refl~ₜ (cong-∘ refl~ₕ (sym~ₕ $ p~⟦p⟧))) ⟩ 
  lam (⟦ t ⟧ `[ < ⟦ σ ⟧ˢ ∘ p , q > ])
    ≈⟨ sym~ₜ (lamCm ⟦ t ⟧ ⟦ σ ⟧ˢ) ⟩
  lam ⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]
    ∎
  where open EqR (TermS {_})
        help : < ⟦ map weaken~ σ ⟧ˢ , q > ~ₕ < ⟦ σ ⋆ p~ ⟧ˢ , q >
        help rewrite sym (mapWk-⋆p σ) = refl~ₕ

⟦⟧-∘-dist [] γ = sym~ₕ (∘<> ⟦ γ ⟧ˢ)
⟦⟧-∘-dist (t ∷ σ) γ = begin
  < ⟦ σ ⋆ γ ⟧ˢ , ⟦ t [ γ ] ⟧ >            ≈⟨ cong-<,> refl~ₜ (⟦⟧-∘-dist σ γ) ⟩ 
  < ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ , ⟦ t [ γ ] ⟧ >       ≈⟨ cong-<,> ([]-comm t γ) refl~ₕ ⟩
  < ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ , ⟦ t ⟧ `[ ⟦ γ ⟧ˢ ] > ≈⟨ sym~ₕ (maps ⟦ t ⟧ ⟦ σ ⟧ˢ ⟦ γ ⟧ˢ) ⟩
  < ⟦ σ ⟧ˢ , ⟦ t ⟧ > ∘ ⟦ γ ⟧ˢ             ∎
  where open EqR (HomS {_} {_})
  
---------------------------------------------------------------------------------------------------
-- Inverses

-- A scope safe term mapped to the cwf world returns the same

ws∘cwf : ∀ {n} (t : Tm-λ n) → t ≡ ⟪ ⟦ t ⟧ ⟫

-- A cwf term mapped to a scope safe term returns the same

cwf∘ws : ∀ {n} (t : Tm-cwf n) → t ~ₜ ⟦ ⟪ t ⟫ ⟧

-- A Hom turned into a substitution and back returns the same

hom∘sub : ∀ {m n} (h : Hom m n) → h ~ₕ ⟦ ⟪ h ⟫ʰ ⟧ˢ

-- t ∈ Tm-λ n ⇒ ⟪ ⟦ t ⟧ ⟫ ~ t
 
ws∘cwf (ƛ t) = cong-ƛ (ws∘cwf t)
ws∘cwf (t · u) = cong-ap (ws∘cwf t) (ws∘cwf u)
ws∘cwf (var zero) = refl
ws∘cwf (var (suc i))
  rewrite sym $ lookup-p i
    = cong (_[ p~ ]) (ws∘cwf (var i))

-- t ∈ Tm-cwf n ⇒ ⟦ ⟪ t ⟫ ⟧ ~ t

cwf∘ws q = refl~ₜ
cwf∘ws (lam t) = cong-lam (cwf∘ws t) 
cwf∘ws (app t u) = cong-app (cwf∘ws t) (cwf∘ws u)
cwf∘ws (t `[ us ]) = sym~ₜ $ begin
  ⟦ ⟪ t ⟫ [ ⟪ us ⟫ʰ ] ⟧        ≈⟨ []-comm ⟪ t ⟫ ⟪ us ⟫ʰ ⟩
  ⟦ ⟪ t ⟫ ⟧ `[ ⟦ ⟪ us ⟫ʰ ⟧ˢ ]  ≈⟨ sym~ₜ (cong-[] (cwf∘ws t) refl~ₕ) ⟩
  t `[ ⟦ ⟪ us ⟫ʰ ⟧ˢ ]          ≈⟨ sym~ₜ (cong-[] refl~ₜ (hom∘sub us)) ⟩
  t `[ us ]                    ∎
  where open EqR (TermS {_})

-- h ∈ Hom m n ⇒ ⟦ ⟪ h ⟫ ⟧ ~ h

hom∘sub (id {zero}) = id₀
hom∘sub (id {suc m}) = begin
  id {1 + m}                ≈⟨ varp ⟩
  < p , q >                 ≈⟨ cong-<,> refl~ₜ p~⟦p⟧ ⟩ 
  < ⟦ p~ ⟧ˢ , q >           ∎
  where open EqR (HomS {_} {_})

hom∘sub (γ ∘ δ) = sym~ₕ $ begin
  ⟦ ⟪ γ ⟫ʰ ⋆ ⟪ δ ⟫ʰ ⟧ˢ       ≈⟨ ⟦⟧-∘-dist ⟪ γ ⟫ʰ ⟪ δ ⟫ʰ ⟩
  ⟦ ⟪ γ ⟫ʰ ⟧ˢ ∘ ⟦ ⟪ δ ⟫ʰ ⟧ˢ  ≈⟨ sym~ₕ (cong-∘ (hom∘sub γ) refl~ₕ) ⟩ 
  γ ∘ ⟦ ⟪ δ ⟫ʰ ⟧ˢ            ≈⟨ sym~ₕ (cong-∘ refl~ₕ (hom∘sub δ)) ⟩ 
  γ ∘ δ                      ∎
  where open EqR (HomS {_} {_})
 
hom∘sub p = p~⟦p⟧

hom∘sub <> = refl~ₕ
hom∘sub < γ , x > = begin
  < γ , x >                    ≈⟨ cong-<,> refl~ₜ (hom∘sub γ) ⟩
  < ⟦ ⟪ γ ⟫ʰ ⟧ˢ , x >          ≈⟨ cong-<,> (cwf∘ws x) refl~ₕ ⟩ 
  < ⟦ ⟪ γ ⟫ʰ ⟧ˢ , ⟦ ⟪ x ⟫ ⟧ >  ∎
  where open EqR (HomS {_} {_})

postulate obv : ∀ n → pNorm (suc n) ~ₕ ⟦ p~ ⟧ˢ

lemmaₚ zero = refl~ₕ
lemmaₚ (suc n) = obv n
