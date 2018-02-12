-----------------------------------------------------------------------------------------------
-- The isomorphism at the raw level between two ΠU-cwfs objects (defined in ExpCwf and Lambda)
-- We show there is an isomorphism of base categories and a natural isomorphism between
-- the functors
-----------------------------------------------------------------------------------------------
module Ext-Typed.DTyped.RawIso where

open import Data.Fin
open import Function as F using (_$_)
open import Ext-Typed.DTyped.Lambda renaming (Tm to Tm-λ ; Sub to Sub-λ ; q to q-λ ; id to id-λ ; p to p-λ ; _∘_ to _∘λ_ ; _[_] to _[_]λ) hiding (subComp ; cong-sub ; pCons)
open import Ext-Typed.DTyped.ExpCwf renaming (Ctx to Ctx-cwf ; Tm to Tm-cwf ; Sub to Sub-cwf)
open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_] ; cong-app)
import Relation.Binary.EqReasoning as EqR

-----------------------------------------------------------------------------------------------
-- Proofs

-- Natural transformations between the functors of the cwfs
⟦_⟧  : ∀ {n} → Tm-λ n → Tm-cwf n
⟪_⟫ : ∀ {n} → Tm-cwf n → Tm-λ n

-- Functors between the base categories of the cwfs
⟦_⟧' : ∀ {m n} → Sub-λ m n → Sub-cwf m n
⟪_⟫' : ∀ {m n} → Sub-cwf m n → Sub-λ m n

-- Variable representation in the variable free calculus
varCwf : ∀ {n} (i : Fin n) → Tm-cwf n 
varCwf zero    = q
varCwf (suc i) = varCwf i [ p ]

⟦ var i ⟧ = varCwf i
⟦ ƛ t   ⟧ = lam ⟦ t ⟧
⟦ t · u ⟧ = app ⟦ t ⟧ ⟦ u ⟧
⟦ Π A B ⟧ = Π ⟦ A ⟧ ⟦ B ⟧
⟦ U     ⟧ = U

⟪ q       ⟫ = q-λ
⟪ t [ γ ] ⟫ = ⟪ t ⟫ [ ⟪ γ ⟫' ]λ
⟪ lam t   ⟫ = ƛ ⟪ t ⟫
⟪ app t u ⟫ = ⟪ t ⟫ · ⟪ u ⟫
⟪ Π A B   ⟫ = Π ⟪ A ⟫ ⟪ B ⟫
⟪ U       ⟫ = U

⟦ []    ⟧' = <>
⟦ t ∷ ρ ⟧' = < ⟦ ρ ⟧' , ⟦ t ⟧ >

⟪ id        ⟫' = id-λ
⟪ γ ∘ γ'    ⟫' = ⟪ γ ⟫' ∘λ ⟪ γ' ⟫'
⟪ p         ⟫' = p-λ
⟪ <>        ⟫' = []
⟪ < γ , t > ⟫' = ⟪ γ ⟫' , ⟪ t ⟫

postulate

  ⟦⟧-∘-dist : ∀ {m n k} (σ : Sub-λ n k) (γ : Sub-λ m n) → ⟦ σ ∘λ γ ⟧' ≋ ⟦ σ ⟧' ∘ ⟦ γ ⟧'

  p-inverse : ∀ {n} → p {n} ≋ ⟦ p-λ ⟧'

sub-comm : ∀ {m n} (t : Tm-λ n) (σ : Sub-λ m n) → ⟦ t [ σ ]λ ⟧ ≈ ⟦ t ⟧ [ ⟦ σ ⟧' ]
sub-comm (var zero)    (t ∷ σ) = sym≈ (qCons ⟦ t ⟧ ⟦ σ ⟧')
sub-comm (var (suc i)) (t ∷ σ) = begin
  ⟦ lookup i σ ⟧                         ≈⟨ sub-comm (var i) σ ⟩
  ⟦ var i ⟧ [ ⟦ σ ⟧' ]                   ≈⟨ cong-sub refl≈ (pCons ⟦ t ⟧ ⟦ σ ⟧') ⟩
  ⟦ var i ⟧ [ p ∘ < ⟦ σ ⟧' , ⟦ t ⟧ > ]   ≈⟨ subComp ⟦ var i ⟧ p < ⟦ σ ⟧' , ⟦ t ⟧ > ⟩
  ⟦ var i ⟧ [ p ] [ < ⟦ σ ⟧' , ⟦ t ⟧ > ] ∎
                                         where open EqR (TmSetoid {_})
sub-comm (t · u) σ =
  trans≈ (cong-app (sub-comm t σ) (sub-comm u σ))
         (subApp ⟦ σ ⟧' ⟦ t ⟧ ⟦ u ⟧)
sub-comm U       _ = sym≈ subU
sub-comm (ƛ t)   σ = {!!}
sub-comm (Π A B) σ = begin
  Π ⟦ A [ σ ]λ ⟧ ⟦ B [ ↑ σ ]λ ⟧                              ≈⟨ cong-Π (sub-comm A σ) (sub-comm B (↑ σ)) ⟩
  Π (⟦ A ⟧ [ ⟦ σ ⟧' ]) (⟦ B ⟧ [ < ⟦ wk-sub σ ⟧' , q > ])     ≈⟨ {!!} ⟩
  Π (⟦ A ⟧ [ ⟦ σ ⟧' ]) (⟦ B ⟧ [ < ⟦ σ ∘λ p-λ ⟧' , q > ])     ≈⟨ cong-Π refl≈ (cong-sub refl≈ (cong-<, (⟦⟧-∘-dist σ p-λ))) ⟩
  Π (⟦ A ⟧ [ ⟦ σ ⟧' ]) (⟦ B ⟧ [ < ⟦ σ ⟧' ∘ ⟦ p-λ ⟧' , q > ]) ≈⟨ cong-Π refl≈ (cong-sub refl≈ (cong-<, (cong-∘₂ (sym≋ p-inverse)))) ⟩
  Π (⟦ A ⟧ [ ⟦ σ ⟧' ]) (⟦ B ⟧ [ < ⟦ σ ⟧' ∘ p , q > ])        ≈⟨ sym≈ (subΠ ⟦ σ ⟧' ⟦ A ⟧ ⟦ B ⟧) ⟩
  Π ⟦ A ⟧ ⟦ B ⟧ [ ⟦ σ ⟧' ]                                   ∎
  where open EqR (TmSetoid {_})

t-λ⇒cwf : ∀ {n} (t : Tm-λ n) → ⟪ ⟦ t ⟧ ⟫ ≡ t

t-cwf⇒λ : ∀ {n} (t : Tm-cwf n) → ⟦ ⟪ t ⟫ ⟧ ≈ t

t-λ⇒cwf (var zero) = refl
t-λ⇒cwf (var (suc i)) = {!!}
t-λ⇒cwf (ƛ t)   = cong ƛ (t-λ⇒cwf t)
t-λ⇒cwf (t · u) = cong₂ _·_ (t-λ⇒cwf t) (t-λ⇒cwf u)
t-λ⇒cwf (Π A B) = cong₂ Π (t-λ⇒cwf A) (t-λ⇒cwf B)
t-λ⇒cwf U       = refl

t-cwf⇒λ q         = refl≈
t-cwf⇒λ (t [ γ ]) = trans≈ (sub-comm ⟪ t ⟫ ⟪ γ ⟫') (cong-sub (t-cwf⇒λ t) {!!})
t-cwf⇒λ (lam t)   = cong-lam (t-cwf⇒λ t)
t-cwf⇒λ (app t u) = cong-app (t-cwf⇒λ t) (t-cwf⇒λ u)
t-cwf⇒λ (Π A B)   = cong-Π (t-cwf⇒λ A) (t-cwf⇒λ B)
t-cwf⇒λ U         = refl≈
