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
open import Unityped.ExpSub.UcwfExpSub renaming (Sub to Sub-cwf ; Tm to Tm-cwf ; Tm-Ucwf to Ucwf-c)
open import Unityped.ImpSub
  renaming (Tm to Tm-λ ; _∘_ to _∘λ_ ; Subst to Sub-λ ; p to p-λ ; _[_] to _[_]λ
            ; id to id-λ ; weaken to weaken-λ ; q to q-λ ; qCons to qCons-λ
            ; subComp to subComp-λ ; pCons to pCons-λ ; cong-∘ to cong-∘λ
            ; compExt to compExt-λ ; id₀ to id₀-λ ; idExt to idExt-λ ; Tm-ucwf to Ucwf-λ)
  hiding (Sub)
open import Unityped.ExpSub.Projection
open import Unityped.ImpSub.Properties
open import Unityped.Ucwf
open import Relation.Binary.PropositionalEquality hiding ([_] ; cong-app)
import Relation.Binary.EqReasoning as EqR

---------------------------------------------------------------------------------------------------
-- The λ-ucwf morphisms between the instances of explicit and implicit substitutions

-- The translation functions (morphisms)

⟦_⟧  : ∀ {n} → Tm-λ n → Tm-cwf n
⟦_⟧' : ∀ {m n} → Sub-λ m n → Sub-cwf m n
⟪_⟫  : ∀ {n} → Tm-cwf n → Tm-λ n
⟪_⟫' : ∀ {m n} → Sub-cwf m n → Sub-λ m n

-- Substitutions as vectors to explicit substitutions

⟦ [] ⟧'    = <>
⟦ t ∷ ts ⟧' = < ⟦ ts ⟧' , ⟦ t ⟧ >

-- Ordinary lambda terms to ucwf combinator terms

⟦ var i ⟧ = PProof.varCwf i
⟦ ƛ t ⟧   = lam ⟦ t ⟧
⟦ t · u ⟧ = app ⟦ t ⟧ ⟦ u ⟧

-- Ucwf combinator terms to lambda terms
-- substitution is a constructor which is mapped to the meta operation

⟪ q ⟫        = q-λ
⟪ t [ us ] ⟫ = ⟪ t ⟫ [ ⟪ us ⟫' ]λ
⟪ lam t ⟫    = ƛ ⟪ t ⟫
⟪ app t u ⟫  = ⟪ t ⟫ · ⟪ u ⟫

-- Explicit substitutions to vectors

⟪ id ⟫'         = id-λ
⟪ ts ∘ us ⟫'    = ⟪ ts ⟫' ∘λ ⟪ us ⟫'
⟪ p ⟫'          = p-λ
⟪ <> ⟫'         = []
⟪ < ts , t > ⟫' = ⟪ ts ⟫' , ⟪ t ⟫

-- Ucwf morphism

Cwf⇒λ-morphism : Ucwf-Morphism Ucwf-c Ucwf-λ
Cwf⇒λ-morphism = record
                   { ⟦_⟧  = ⟪_⟫
                   ; ⟦_⟧' = ⟪_⟫'
                   ; id-preserved  = refl
                   ; q-preserved   = refl
                   ; p-preserved   = refl
                   ; ∘-preserved   = λ _ _ → refl
                   ; <>-preserved  = refl
                   ; <,>-preserved = λ _ _ → refl
                   ; sub-preserved = λ _ _ → refl
                   }

---------------------------------------------------------------------------------------------------
-- Proofs that the translation functions are inverses of each other

-- Auxiliary props

lemmaₚ : ∀ n → PProof.pNorm n ≋ ⟦ p-λ ⟧'
  
p-inverse : ∀ {n} → p ≋ ⟦ p-λ ⟧'
p-inverse {n} = sym≋ $ trans≋ (sym≋ $ lemmaₚ n)
                           (sym≋ $ PProof.p~vars n)

-- Composition is preserved from the map

∘-preserves : ∀ {m n k} (σ : Sub-λ n k) (γ : Sub-λ m n)
              → ⟦ σ ∘λ γ ⟧' ≋ ⟦ σ ⟧' ∘ ⟦ γ ⟧'

-- Substitution is preserved from the map

sub-preserves : ∀ {m n} (t : Tm-λ n) (σ : Sub-λ m n)
                → ⟦ t [ σ ]λ ⟧ ≈ ⟦ t ⟧ [ ⟦ σ ⟧' ]

sub-preserves (var zero)    (x ∷ σ) = sym≈ (qCons ⟦ σ ⟧' ⟦ x ⟧)
sub-preserves (var (suc ι)) (x ∷ σ) = sym≈ $ begin
  ⟦ var ι ⟧ [ p ] [ < ⟦ σ ⟧' , ⟦ x ⟧ > ]
    ≈⟨ sym≈ (subComp p < ⟦ σ ⟧' , ⟦ x ⟧ > ⟦ var ι ⟧) ⟩
  ⟦ var ι ⟧ [ p ∘ < ⟦ σ ⟧' , ⟦ x ⟧ > ]
    ≈⟨ (cong-sub₂ (pCons ⟦ σ ⟧' ⟦ x ⟧)) ⟩
  ⟦ var ι ⟧ [ ⟦ σ ⟧' ]
    ≈⟨ sym≈ (sub-preserves (var ι) σ) ⟩
  ⟦ lookup ι σ ⟧
    ∎
  where open EqR (TmSetoid {_})

sub-preserves (t · u) σ = begin
  app ⟦ t [ σ ]λ ⟧ ⟦ u [ σ ]λ ⟧
    ≈⟨ cong-app (sub-preserves t σ) refl≈ ⟩
  app (⟦ t ⟧ [ ⟦ σ ⟧' ]) (⟦ u [ σ ]λ ⟧)
    ≈⟨ cong-app refl≈ (sub-preserves u σ) ⟩
  app (⟦ t ⟧ [ ⟦ σ ⟧' ]) (⟦ u ⟧ [ ⟦ σ ⟧' ])
    ≈⟨ subApp ⟦ σ ⟧' ⟦ t ⟧ ⟦ u ⟧ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ [ ⟦ σ ⟧' ]
    ∎
  where open EqR (TmSetoid {_})

sub-preserves (ƛ t) σ = begin
  lam ⟦ t [ ↑ σ ]λ ⟧
    ≈⟨ cong-lam $ sub-preserves t (↑ σ) ⟩
  lam (⟦ t ⟧ [ < ⟦ map weaken-λ σ ⟧' , q > ])
    ≈⟨ cong-lam $ cong-sub₂ help ⟩
  lam (⟦ t ⟧ [ < ⟦ σ ∘λ p-λ ⟧' , q > ])
    ≈⟨ cong-lam $ cong-sub₂ (cong-<, ({!!})) ⟩ 
  lam (⟦ t ⟧ [ < ⟦ σ ⟧' ∘ ⟦ p-λ ⟧' , q > ])
    ≈⟨ cong-lam $ cong-sub₂ (cong-<, (cong-∘₂ (sym≋ $ p-inverse))) ⟩ 
  lam (⟦ t ⟧ [ < ⟦ σ ⟧' ∘ p , q > ])
    ≈⟨ sym≈ (subLam ⟦ σ ⟧' ⟦ t ⟧) ⟩
  lam ⟦ t ⟧ [ ⟦ σ ⟧' ]
    ∎
  where open EqR (TmSetoid {_})
        help : < ⟦ map weaken-λ σ ⟧' , q > ≋ < ⟦ σ ∘λ p-λ ⟧' , q >
        help rewrite sym (mapWk-∘p σ) = refl≋

∘-preserves [] γ = sym≋ (left-zero ⟦ γ ⟧')
∘-preserves (t ∷ σ) γ = begin
  < ⟦ σ ∘λ γ ⟧' , ⟦ t [ γ ]λ ⟧ >
    ≈⟨ cong-<, (∘-preserves σ γ) ⟩ 
  < ⟦ σ ⟧' ∘ ⟦ γ ⟧' , ⟦ t [ γ ]λ ⟧ >
    ≈⟨ cong-,> (sub-preserves t γ) ⟩
  < ⟦ σ ⟧' ∘ ⟦ γ ⟧' , ⟦ t ⟧ [ ⟦ γ ⟧' ] >
    ≈⟨ sym≋ (compExt ⟦ σ ⟧' ⟦ γ ⟧' ⟦ t ⟧) ⟩
  < ⟦ σ ⟧' , ⟦ t ⟧ > ∘ ⟦ γ ⟧'
    ∎
  where open EqR (SubSetoid {_} {_})
  
---------------------------------------------------------------------------------------------------
-- Inverses

-- A scope safe term mapped to the cwf world returns the same

tm-λ⇒cwf : ∀ {n} (t : Tm-λ n) → t ≡ ⟪ ⟦ t ⟧ ⟫

-- A cwf term mapped to a scope safe term returns the same

tm-cwf⇒λ : ∀ {n} (t : Tm-cwf n) → t ≈ ⟦ ⟪ t ⟫ ⟧

-- A Sub mapped to a vector substitution returns the same

sub-cwf⇒λ : ∀ {m n} (h : Sub-cwf m n) → h ≋ ⟦ ⟪ h ⟫' ⟧'

-- A vector substitution mapped to a hom returns the same

sub-λ⇒cwf : ∀ {m n} (ρ : Sub-λ m n) → ρ ≡ ⟪ ⟦ ρ ⟧' ⟫'

tm-λ⇒cwf (ƛ t) = cong ƛ (tm-λ⇒cwf t)
tm-λ⇒cwf (t · u) = cong₂ _·_ (tm-λ⇒cwf t) (tm-λ⇒cwf u)
tm-λ⇒cwf (var zero) = refl
tm-λ⇒cwf (var (suc i))
  rewrite sym $ lookup-p i = cong (_[ p-λ ]λ) (tm-λ⇒cwf (var i))

tm-cwf⇒λ q = refl≈
tm-cwf⇒λ (lam t) = cong-lam (tm-cwf⇒λ t) 
tm-cwf⇒λ (app t u) = cong-app (tm-cwf⇒λ t) (tm-cwf⇒λ u)
tm-cwf⇒λ (t [ us ]) = sym≈ $ begin
  ⟦ ⟪ t ⟫ [ ⟪ us ⟫' ]λ ⟧
    ≈⟨ sub-preserves ⟪ t ⟫ ⟪ us ⟫' ⟩
  ⟦ ⟪ t ⟫ ⟧ [ ⟦ ⟪ us ⟫' ⟧' ]
    ≈⟨ sym≈ (cong-sub₁ (tm-cwf⇒λ t)) ⟩
  t [ ⟦ ⟪ us ⟫' ⟧' ]
    ≈⟨ sym≈ (cong-sub₂ (sub-cwf⇒λ us)) ⟩
  t [ us ]
    ∎
  where open EqR (TmSetoid {_})

sub-cwf⇒λ (id {zero}) = id₀
sub-cwf⇒λ (id {suc m}) = begin
  id {1 + m}
    ≈⟨ idExt ⟩
  < p , q >
    ≈⟨ cong-<, (sub-cwf⇒λ p) ⟩ 
  < ⟦ p-λ ⟧' , q >
    ∎
  where open EqR (SubSetoid {_} {_})

sub-cwf⇒λ (γ ∘ δ) = sym≋ $ begin
  ⟦ ⟪ γ ⟫' ∘λ ⟪ δ ⟫' ⟧'
    ≈⟨ ∘-preserves ⟪ γ ⟫' ⟪ δ ⟫' ⟩
  ⟦ ⟪ γ ⟫' ⟧' ∘ ⟦ ⟪ δ ⟫' ⟧'
    ≈⟨ sym≋ (cong-∘₁ (sub-cwf⇒λ γ)) ⟩ 
  γ ∘ ⟦ ⟪ δ ⟫' ⟧'
    ≈⟨ sym≋ (cong-∘₂ (sub-cwf⇒λ δ)) ⟩ 
  γ ∘ δ
    ∎
  where open EqR (SubSetoid {_} {_})
 
sub-cwf⇒λ p = p-inverse

sub-cwf⇒λ <> = refl≋
sub-cwf⇒λ < γ , x > = cong-<,> (tm-cwf⇒λ x) (sub-cwf⇒λ γ)

sub-λ⇒cwf [] = refl
sub-λ⇒cwf (x ∷ ρ) = cong₂ _,_ (sub-λ⇒cwf ρ) (tm-λ⇒cwf x)

---------------------------------------------------------------------------
-- Lemmas for the projection inverse

open Fins
open PProof

⟦map⟧≈map : ∀ {m n} (is : Fins m n)
            → ⟦ mapTT var is ⟧' ≋ mapT varCwf is
⟦map⟧≈map <>         = refl≋
⟦map⟧≈map < is , x > = cong-<, (⟦map⟧≈map is)

lm-p : ∀ n → vars (pFins n) ≋ ⟦ mapTT var (pFins n) ⟧'
lm-p n = trans≋ (vars-map (pFins n)) (sym≋ (⟦map⟧≈map (pFins n)))

lemmaₚ n rewrite sym (pp=p~ n) =
  trans≋ (vars-map (pFins n))
         (sym≋ (⟦map⟧≈map (pFins n)))
          
