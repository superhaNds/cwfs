---------------------------------------------------------------------------------------------------
-- Contains the definitions of the bijections between the setoids of wellscoped terms and terms as
-- a Ucwf. Moreover, a proof that they are inverses of each other, which means they are isomorphic
---------------------------------------------------------------------------------------------------

module Unityped.Isomorphism where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_$_ ; flip)
open import Unityped.UcwfModel renaming (_[_] to _`[_])
open import Unityped.Wellscoped
  renaming (p to p~ ; p′ to p′~ ; id to id~ ; weakenₛ to weaken~ ; q to q~)
  hiding (maps)
open import Unityped.Wellscoped.Properties  
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.EqReasoning as EqR

---------------------------------------------------------------------------------------------------
-- The bijection between wellscoped terms and terms as a Ucwf

-- The translation functions (morphisms)

⟦_⟧  : ∀ {n} → Term n → CwfTm n
⟦_⟧ₛ : ∀ {m n} → Subst m n → Hom m n
⟪_⟫  : ∀ {n} → CwfTm n → Term n
⟪_⟫ₕ : ∀ {m n} → Hom m n → Subst m n

-- Substitutions as vectors to a Hom

⟦ [] ⟧ₛ    = <>
⟦ t ∷ σ ⟧ₛ = < ⟦ σ ⟧ₛ , ⟦ t ⟧ > 

-- Traditional lambda calculus terms to Ucwf terms

⟦ var zero ⟧    = q
⟦ var (suc ι) ⟧ = weaken ⟦ var ι ⟧
⟦ ƛ t ⟧         = lam ⟦ t ⟧
⟦ t · u ⟧       = app ⟦ t ⟧ ⟦ u ⟧

-- Ucwf terms to lambda terms, (substitution is a constructor which is mapped to the meta operation)

⟪ q ⟫         = q~
⟪ t `[ us ] ⟫ = ⟪ t ⟫ [ ⟪ us ⟫ₕ ]
⟪ lam t ⟫     = ƛ ⟪ t ⟫
⟪ app t u ⟫   = ⟪ t ⟫ · ⟪ u ⟫

-- Homs to vector substitutions

⟪ id n ⟫ₕ       = id~ n
⟪ ts ∘ us ⟫ₕ    = ⟪ ts ⟫ₕ ⋆ ⟪ us ⟫ₕ
⟪ p n ⟫ₕ        = p~ n
⟪ <> ⟫ₕ         = []
⟪ < ts , t > ⟫ₕ = ⟪ ts ⟫ₕ ∙ ⟪ t ⟫

---------------------------------------------------------------------------------------------------
-- Proofs that the translation functions are inverses of each other

-- A scope safe term mapped to the cwf world returns the same

ws∘cwf : ∀ {n} (t : Term n) → t ≡ ⟪ ⟦ t ⟧ ⟫

-- A cwf term mapped to a scope safe term returns the same

cwf∘ws : ∀ {n} (t : CwfTm n) → t ~ₜ ⟦ ⟪ t ⟫ ⟧

-- A substitution turned into a Hom and back returns the same

sub∘hom : ∀ {m n} (σ : Subst m n) → σ ≡ ⟪ ⟦ σ ⟧ₛ ⟫ₕ

-- A Hom turned into a substitution and back returns the same

hom∘sub : ∀ {m n} (h : Hom m n) → h ~ₕ ⟦ ⟪ h ⟫ₕ ⟧ₛ

gen-p : ∀ m n → p′ m n ~ₕ ⟦ p′~ m n ⟧ₛ
gen-p m zero rewrite p′0=[] {m} = p′0~<>
gen-p m (suc n) = begin
  p′ m (1 + n)                                   ≈⟨ eta $ p′ m (1 + n) ⟩
  < p n ∘ p′ m (1 + n) , q `[ p′ m (1 + n) ] >   ≈⟨ {!!} ⟩
  ⟦ p′~ m (1 + n) ⟧ₛ                             ∎
  where open EqR (HomS {_} {_})

p~⟦p⟧ : ∀ n → p n ~ₕ ⟦ p~ n ⟧ₛ
p~⟦p⟧ n = begin
  p n               ≈⟨ sym~ₕ (idL (p n)) ⟩
  id n ∘ p n        ≈⟨ gen-p 1 n ⟩
  ⟦ id~ n ⋆ p~ n ⟧ₛ ≈⟨ help ⟩
  ⟦ p~ n ⟧ₛ         ∎
  where open EqR (HomS {_} {_})
        help : ⟦ id~ n ⋆ p~ n ⟧ₛ ~ₕ ⟦ p~ n ⟧ₛ
        help rewrite ∘-lid (p~ n) = refl~ₕ

-- Interpreting a substitution commutes

[]-comm : ∀ {m n} (t : Term n) (σ : Subst m n) → ⟦ t [ σ ] ⟧ ~ₜ ⟦ t ⟧ `[ ⟦ σ ⟧ₛ ]

[]-comm (var zero)    (x ∷ σ) = qCons ⟦ x ⟧ ⟦ σ ⟧ₛ
[]-comm (var (suc ι)) (x ∷ σ) = sym~ₜ $ begin
  ⟦ var ι ⟧ `[ p _ ] `[ < ⟦ σ ⟧ₛ , ⟦ x ⟧ > ] ≈⟨ sym~ₜ (clos ⟦ var ι ⟧ (p _) < ⟦ σ ⟧ₛ , ⟦ x ⟧ >) ⟩
  ⟦ var ι ⟧ `[ p _ ∘ < ⟦ σ ⟧ₛ , ⟦ x ⟧ > ]    ≈⟨ sym~ₜ (congh~ₜ (_`[_] ⟦ var ι ⟧) (pCons ⟦ x ⟧ ⟦ σ ⟧ₛ)) ⟩
  ⟦ var ι ⟧ `[ ⟦ σ ⟧ₛ ]                      ≈⟨ sym~ₜ ([]-comm (var ι) σ) ⟩
  ⟦ lookup ι σ ⟧                             ∎
  where open EqR (CwfTmS {_})

[]-comm (t · u) σ = begin
  app ⟦ t [ σ ] ⟧ ⟦ u [ σ ] ⟧                  ≈⟨ cong~ₜ (flip app ⟦ u [ σ ] ⟧) ([]-comm t σ) ⟩
  app (⟦ t ⟧ `[ ⟦ σ ⟧ₛ ]) (⟦ u [ σ ] ⟧)        ≈⟨ cong~ₜ (app (⟦ t ⟧ `[ ⟦ σ ⟧ₛ ])) ([]-comm u σ) ⟩
  app (⟦ t ⟧ `[ ⟦ σ ⟧ₛ ]) (⟦ u ⟧ `[ ⟦ σ ⟧ₛ ])  ≈⟨ appCm ⟦ t ⟧ ⟦ u ⟧ ⟦ σ ⟧ₛ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ `[ ⟦ σ ⟧ₛ ]                  ∎
  where open EqR (CwfTmS {_})
  
[]-comm (ƛ t) σ = begin
  lam ⟦ t [ ↑ₛ σ ] ⟧                            ≈⟨ cong~ₜ lam ([]-comm t (↑ₛ σ)) ⟩
  lam (⟦ t ⟧ `[ < ⟦ map weaken~ σ ⟧ₛ , q > ]) ≈⟨ congh~ₜ (λ x → lam (⟦ t ⟧ `[ x ])) help ⟩
  lam (⟦ t ⟧ `[ < ⟦ σ ⋆ p~ _ ⟧ₛ , q > ])      ≈⟨ congh~ₜ (λ x → lam (⟦ t ⟧ `[ < x , q > ])) {!!} ⟩
  lam (⟦ t ⟧ `[ < ⟦ σ ⟧ₛ ∘ ⟦ p~ _ ⟧ₛ , q > ]) ≈⟨ congh~ₜ (λ x → lam (⟦ t ⟧ `[ < ⟦ σ ⟧ₛ ∘ x , q > ]))
                                                           (sym~ₕ (p~⟦p⟧ _)) ⟩
  lam (⟦ t ⟧ `[ < ⟦ σ ⟧ₛ ∘ p _ , q > ])       ≈⟨ sym~ₜ (lamCm ⟦ t ⟧ ⟦ σ ⟧ₛ) ⟩
  lam ⟦ t ⟧ `[ ⟦ σ ⟧ₛ ]                         ∎
  where open EqR (CwfTmS {_})
        help : < ⟦ map weaken~ σ ⟧ₛ , q > ~ₕ < ⟦ σ ⋆ p~ _ ⟧ₛ , q >
        help rewrite sym (mapWk-⋆p σ) = refl~ₕ

-- Interpreting a composition distributes

⟦⟧-∘-dist : ∀ {m n k} (σ : Subst n k) (γ : Subst m n) → ⟦ σ ⋆ γ ⟧ₛ ~ₕ ⟦ σ ⟧ₛ ∘ ⟦ γ ⟧ₛ

⟦⟧-∘-dist [] γ = sym~ₕ (∘<> ⟦ γ ⟧ₛ)
⟦⟧-∘-dist (t ∷ σ) γ = begin
  < ⟦ σ ⋆ γ ⟧ₛ , ⟦ t [ γ ] ⟧ >            ≈⟨ cong~ₕ (λ z → < z , _ >) (⟦⟧-∘-dist σ γ) ⟩
  < ⟦ σ ⟧ₛ ∘ ⟦ γ ⟧ₛ , ⟦ t [ γ ] ⟧ >       ≈⟨ congt~ₕ (λ z → < _ , z >) ([]-comm t γ) ⟩
  < ⟦ σ ⟧ₛ ∘ ⟦ γ ⟧ₛ , ⟦ t ⟧ `[ ⟦ γ ⟧ₛ ] > ≈⟨ sym~ₕ (maps ⟦ t ⟧ ⟦ σ ⟧ₛ ⟦ γ ⟧ₛ) ⟩
  < ⟦ σ ⟧ₛ , ⟦ t ⟧ > ∘ ⟦ γ ⟧ₛ             ∎
  where open EqR (HomS {_} {_})

-- t ∈ Term n ⇒ ⟪ ⟦ t ⟧ ⟫ ≡ t

ws∘cwf (var zero) = refl
ws∘cwf (var (suc ι)) = sym $ trans (sym $ cong (_[ p~ _ ]) (ws∘cwf (var ι))) (lookup-p ι)
ws∘cwf (ƛ t) = cong ƛ (ws∘cwf t)
ws∘cwf (t · u) = cong₂ _·_ (ws∘cwf t) (ws∘cwf u)

-- t ∈ UcwfTm n ⇒ ⟦ ⟪ t ⟫ ⟧ ~ t

cwf∘ws q = refl~ₜ
cwf∘ws (lam t) = cong~ₜ lam (cwf∘ws t)
cwf∘ws (app t u) = trans~ₜ (cong~ₜ (app t) (cwf∘ws u)) (cong~ₜ (λ z → app z _) (cwf∘ws t))
cwf∘ws (t `[ us ]) = sym~ₜ $ begin
  ⟦ ⟪ t ⟫ [ ⟪ us ⟫ₕ ] ⟧         ≈⟨ []-comm ⟪ t ⟫ ⟪ us ⟫ₕ ⟩
  ⟦ ⟪ t ⟫ ⟧ `[ ⟦ ⟪ us ⟫ₕ ⟧ₛ ]   ≈⟨ sym~ₜ (cong~ₜ (_`[ ⟦ ⟪ us ⟫ₕ ⟧ₛ ]) (cwf∘ws t)) ⟩
  t `[ ⟦ ⟪ us ⟫ₕ ⟧ₛ ]           ≈⟨ sym~ₜ (congh~ₜ (t `[_]) (hom∘sub us)) ⟩
  t `[ us ]                     ∎
  where open EqR (CwfTmS {_})

-- σ ∈ Subst m n ⇒ ⟪ ⟦ σ ⟧ ⟫ ≡ σ

sub∘hom [] = refl
sub∘hom (t ∷ σ) rewrite sym  (sub∘hom σ)
                      | sym (ws∘cwf t) = refl

-- h ∈ Hom m n ⇒ ⟦ ⟪ h ⟫ ⟧

hom∘sub (id zero) = id₀
hom∘sub (id (suc m)) = begin
  id (1 + m)                  ≈⟨ varp ⟩
  < p m , q >                 ≈⟨ cong~ₕ (<_, q >) (hom∘sub (p m)) ⟩
  < ⟦ p~ m ⟧ₛ , q >           ∎
  where open EqR (HomS {_} {_})

hom∘sub (h ∘ g) = sym~ₕ $ begin
  ⟦ ⟪ h ⟫ₕ ⋆ ⟪ g ⟫ₕ ⟧ₛ          ≈⟨ ⟦⟧-∘-dist ⟪ h ⟫ₕ ⟪ g ⟫ₕ ⟩
  ⟦ ⟪ h ⟫ₕ ⟧ₛ ∘ ⟦ ⟪ g ⟫ₕ ⟧ₛ     ≈⟨ sym~ₕ (cong~ₕ (_∘ ⟦ ⟪ g ⟫ₕ ⟧ₛ) (hom∘sub h)) ⟩
  h ∘ ⟦ ⟪ g ⟫ₕ ⟧ₛ               ≈⟨ sym~ₕ (cong~ₕ (_∘_ h) (hom∘sub g)) ⟩
  h ∘ g                         ∎
  where open EqR (HomS {_} {_})
  
hom∘sub (p n) = p~⟦p⟧ n

hom∘sub <> = refl~ₕ
hom∘sub < h , x > = begin
  < h , x >                     ≈⟨ cong~ₕ (<_, x >) (hom∘sub h) ⟩
  < ⟦ ⟪ h ⟫ₕ ⟧ₛ , x >           ≈⟨ congt~ₕ (λ z → < _ , z >) (cwf∘ws x) ⟩
  < ⟦ ⟪ h ⟫ₕ ⟧ₛ , ⟦ ⟪ x ⟫ ⟧ >   ∎
  where open EqR (HomS {_} {_})
