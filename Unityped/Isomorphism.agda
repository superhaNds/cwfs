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
open import Unityped.UcwfComb renaming (Tm to Tm-cwf)
open import Unityped.Wellscoped
  renaming (Tm to Tm-λ ; _∘_ to _∘λ_ ; Subst to Sub-λ ; p to p-λ ; _[_] to _[_]λ
            ; id to id-λ ; weaken to weaken-λ ; q to q-λ ; qCons to qCons-λ
            ; subComp to subComp-λ ; pCons to pCons-λ ; cong-∘ to cong-∘λ
            ; compExt to compExt-λ ; id₀ to id₀-λ ; idExt to idExt-λ)
  hiding (Sub)
open import Unityped.Projection
open import Unityped.Wellscoped.Properties  
open import Relation.Binary.PropositionalEquality hiding ([_] ; cong-app)
import Relation.Binary.EqReasoning as EqR

---------------------------------------------------------------------------------------------------
-- The bijection between wellscoped λ terms and terms as a Ucwf

-- The translation functions (morphisms)

⟦_⟧  : ∀ {n} → Tm-λ n → Tm-cwf n
⟦_⟧' : ∀ {m n} → Sub-λ m n → Sub m n
⟪_⟫  : ∀ {n} → Tm-cwf n → Tm-λ n
⟪_⟫' : ∀ {m n} → Sub m n → Sub-λ m n

-- Substitutions as vectors to explicit ucwf morphisms

⟦ [] ⟧'    = <>
⟦ t ∷ σ ⟧' = < ⟦ σ ⟧' , ⟦ t ⟧ >

-- Traditional lambda calculus terms to Ucwf combinator terms

⟦ var i ⟧ = PProof.varCwf i
⟦ ƛ t ⟧   = lam ⟦ t ⟧
⟦ t · u ⟧ = app ⟦ t ⟧ ⟦ u ⟧

-- Ucwf terms to lambda terms, (substitution is a constructor which is mapped to the meta operation)

⟪ q ⟫        = q-λ
⟪ t [ us ] ⟫ = ⟪ t ⟫ [ ⟪ us ⟫' ]λ
⟪ lam t ⟫    = ƛ ⟪ t ⟫
⟪ app t u ⟫  = ⟪ t ⟫ · ⟪ u ⟫

-- Subs to vector substitutions

⟪ id ⟫'         = id-λ
⟪ ts ∘ us ⟫'    = ⟪ ts ⟫' ∘λ ⟪ us ⟫'
⟪ p ⟫'          = p-λ
⟪ <> ⟫'         = []
⟪ < ts , t > ⟫' = ⟪ ts ⟫' , ⟪ t ⟫

---------------------------------------------------------------------------------------------------
-- Proofs that the translation functions are inverses of each other

-- Auxiliary props

lemmaₚ : ∀ n → PProof.pNorm n ≋ ⟦ p-λ ⟧'
  
p-inverse : ∀ {n} → p ≋ ⟦ p-λ ⟧'
p-inverse {n} = sym≋ $ trans≋ (sym≋ $ lemmaₚ n)
                           (sym≋ $ PProof.p~vars n)

-- Interpreting a composition distributes

⟦⟧-∘-dist : ∀ {m n k} (σ : Sub-λ n k) (γ : Sub-λ m n) → ⟦ σ ∘λ γ ⟧' ≋ ⟦ σ ⟧' ∘ ⟦ γ ⟧'

-- Interpreting a substitution commutes

[]-comm : ∀ {m n} (t : Tm-λ n) (σ : Sub-λ m n) → ⟦ t [ σ ]λ ⟧ ≈ ⟦ t ⟧ [ ⟦ σ ⟧' ]

[]-comm (var zero)    (x ∷ σ) = sym≈ (qCons ⟦ σ ⟧' ⟦ x ⟧)
[]-comm (var (suc ι)) (x ∷ σ) = sym≈ $ begin
  ⟦ var ι ⟧ [ p ] [ < ⟦ σ ⟧' , ⟦ x ⟧ > ]
    ≈⟨ sym≈ (subComp p < ⟦ σ ⟧' , ⟦ x ⟧ > ⟦ var ι ⟧) ⟩
  ⟦ var ι ⟧ [ p ∘ < ⟦ σ ⟧' , ⟦ x ⟧ > ]
    ≈⟨ (cong-sub refl≈ (pCons ⟦ σ ⟧' ⟦ x ⟧)) ⟩
  ⟦ var ι ⟧ [ ⟦ σ ⟧' ]
    ≈⟨ sym≈ ([]-comm (var ι) σ) ⟩
  ⟦ lookup ι σ ⟧
    ∎
  where open EqR (TmSetoid {_})

[]-comm (t · u) σ = begin
  app ⟦ t [ σ ]λ ⟧ ⟦ u [ σ ]λ ⟧
    ≈⟨ cong-app ([]-comm t σ) refl≈ ⟩
  app (⟦ t ⟧ [ ⟦ σ ⟧' ]) (⟦ u [ σ ]λ ⟧)
    ≈⟨ cong-app refl≈ ([]-comm u σ) ⟩
  app (⟦ t ⟧ [ ⟦ σ ⟧' ]) (⟦ u ⟧ [ ⟦ σ ⟧' ])
    ≈⟨ subApp ⟦ σ ⟧' ⟦ t ⟧ ⟦ u ⟧ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ [ ⟦ σ ⟧' ]
    ∎
  where open EqR (TmSetoid {_})

[]-comm (ƛ t) σ = begin
  lam ⟦ t [ ↑ σ ]λ ⟧
    ≈⟨ cong-lam $ []-comm t (↑ σ) ⟩
  lam (⟦ t ⟧ [ < ⟦ map weaken-λ σ ⟧' , q > ])
    ≈⟨ cong-lam $ cong-sub refl≈ help ⟩
  lam (⟦ t ⟧ [ < ⟦ σ ∘λ p-λ ⟧' , q > ])
    ≈⟨ cong-lam $ cong-sub refl≈
       (cong-<,> refl≈ ({!!})) ⟩ 
  lam (⟦ t ⟧ [ < ⟦ σ ⟧' ∘ ⟦ p-λ ⟧' , q > ])
    ≈⟨ cong-lam $ cong-sub refl≈
       (cong-<,> refl≈ (cong-∘ refl≋ (sym≋ $ p-inverse))) ⟩ 
  lam (⟦ t ⟧ [ < ⟦ σ ⟧' ∘ p , q > ])
    ≈⟨ sym≈ (subLam ⟦ σ ⟧' ⟦ t ⟧) ⟩
  lam ⟦ t ⟧ [ ⟦ σ ⟧' ]
    ∎
  where open EqR (TmSetoid {_})
        help : < ⟦ map weaken-λ σ ⟧' , q > ≋ < ⟦ σ ∘λ p-λ ⟧' , q >
        help rewrite sym (mapWk-∘p σ) = refl≋

⟦⟧-∘-dist [] γ = sym≋ (<>Lzero ⟦ γ ⟧')
⟦⟧-∘-dist (t ∷ σ) γ = begin
  < ⟦ σ ∘λ γ ⟧' , ⟦ t [ γ ]λ ⟧ >
    ≈⟨ cong-<,> refl≈ (⟦⟧-∘-dist σ γ) ⟩ 
  < ⟦ σ ⟧' ∘ ⟦ γ ⟧' , ⟦ t [ γ ]λ ⟧ >
    ≈⟨ cong-<,> ([]-comm t γ) refl≋ ⟩
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

sub-cwf⇒λ : ∀ {m n} (h : Sub m n) → h ≋ ⟦ ⟪ h ⟫' ⟧'

-- A vector substitution mapped to a hom returns the same

sub-λ⇒cwf : ∀ {m n} (ρ : Sub-λ m n) → ρ ≡ ⟪ ⟦ ρ ⟧' ⟫'

-- t ∈ Tm-λ n ⇒ ⟪ ⟦ t ⟧ ⟫ ≡ t
 
tm-λ⇒cwf (ƛ t) = cong-ƛ (tm-λ⇒cwf t)
tm-λ⇒cwf (t · u) = cong-ap (tm-λ⇒cwf t) (tm-λ⇒cwf u)
tm-λ⇒cwf (var zero) = refl
tm-λ⇒cwf (var (suc i))
  rewrite sym $ lookup-p i = cong (_[ p-λ ]λ) (tm-λ⇒cwf (var i))

-- t ∈ Tm-cwf n ⇒ ⟦ ⟪ t ⟫ ⟧ -λ t

tm-cwf⇒λ q = refl≈
tm-cwf⇒λ (lam t) = cong-lam (tm-cwf⇒λ t) 
tm-cwf⇒λ (app t u) = cong-app (tm-cwf⇒λ t) (tm-cwf⇒λ u)
tm-cwf⇒λ (t [ us ]) = sym≈ $ begin
  ⟦ ⟪ t ⟫ [ ⟪ us ⟫' ]λ ⟧     ≈⟨ []-comm ⟪ t ⟫ ⟪ us ⟫' ⟩
  ⟦ ⟪ t ⟫ ⟧ [ ⟦ ⟪ us ⟫' ⟧' ]  ≈⟨ sym≈ (cong-sub (tm-cwf⇒λ t) refl≋) ⟩
  t [ ⟦ ⟪ us ⟫' ⟧' ]          ≈⟨ sym≈ (cong-sub refl≈ (sub-cwf⇒λ us)) ⟩
  t [ us ]                    ∎
  where open EqR (TmSetoid {_})

-- h ∈ Sub m n ⇒ ⟦ ⟪ h ⟫ ⟧ ≈ h

sub-cwf⇒λ (id {zero}) = id₀
sub-cwf⇒λ (id {suc m}) = begin
  id {1 + m}             ≈⟨ idExt ⟩
  < p , q >              ≈⟨ cong-<,> refl≈ (sub-cwf⇒λ p) ⟩ 
  < ⟦ p-λ ⟧' , q >       ∎
  where open EqR (SubSetoid {_} {_})

sub-cwf⇒λ (γ ∘ δ) = sym≋ $ begin
  ⟦ ⟪ γ ⟫' ∘λ ⟪ δ ⟫' ⟧'
    ≈⟨ ⟦⟧-∘-dist ⟪ γ ⟫' ⟪ δ ⟫' ⟩
  ⟦ ⟪ γ ⟫' ⟧' ∘ ⟦ ⟪ δ ⟫' ⟧'
    ≈⟨ sym≋ (cong-∘ (sub-cwf⇒λ γ) refl≋) ⟩ 
  γ ∘ ⟦ ⟪ δ ⟫' ⟧'
    ≈⟨ sym≋ (cong-∘ refl≋ (sub-cwf⇒λ δ)) ⟩ 
  γ ∘ δ
    ∎
  where open EqR (SubSetoid {_} {_})
 
sub-cwf⇒λ p = p-inverse

sub-cwf⇒λ <> = refl≋
sub-cwf⇒λ < γ , x > = cong-<,> (tm-cwf⇒λ x) (sub-cwf⇒λ γ)

sub-λ⇒cwf [] = refl
sub-λ⇒cwf (x ∷ ρ) = cong₂ _,_ (sub-λ⇒cwf ρ) (tm-λ⇒cwf x)

---------------------------------------------------------------------------
-- Lemmas to get the projection inverse proof right.

open Fins
open PProof

⟦map⟧≈map : ∀ {m n} (is : Fins m n) →
            ⟦ mapTT var is ⟧' ≋ mapT varCwf is
⟦map⟧≈map <>         = refl≋
⟦map⟧≈map < is , x > = cong-<,> refl≈ (⟦map⟧≈map is)

lm-p : ∀ n → vars (pFins n) ≋ ⟦ mapTT var (pFins n) ⟧'
lm-p n = trans≋ (vars-map (pFins n)) (sym≋ (⟦map⟧≈map (pFins n)))

lemmaₚ n rewrite sym (pp=p~ n) =
  trans≋ (vars-map (pFins n))
          (sym≋ (⟦map⟧≈map (pFins n)))
          
