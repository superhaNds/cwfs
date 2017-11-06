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
open import Function.Bijection using (Bijection ; Bijective)
open import Unityped.UcwfModel renaming (Term to Tm-cwf ; _[_] to _`[_])
open import Unityped.Wellscoped
  renaming (Term to Tm-λ ; p to p~ ; p′ to p′~ ; id to id~ ; weakenₛ to weaken~ ; q to q~)
  hiding (maps)
open import Unityped.Wellscoped.Properties  
open import Relation.Binary.PropositionalEquality hiding ([_])
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

⟦ var zero ⟧    = q
⟦ var (suc ι) ⟧ = weaken ⟦ var ι ⟧
⟦ ƛ t ⟧         = lam ⟦ t ⟧
⟦ t · u ⟧       = app ⟦ t ⟧ ⟦ u ⟧

-- Ucwf terms to lambda terms, (substitution is a constructor which is mapped to the meta operation)

⟪ q ⟫         = vr 0
⟪ t `[ us ] ⟫ = ⟪ t ⟫ [ ⟪ us ⟫ʰ ]
⟪ lam t ⟫     = ƛ ⟪ t ⟫
⟪ app t u ⟫   = ⟪ t ⟫ · ⟪ u ⟫

-- Homs to vector substitutions

⟪ id n ⟫ʰ       = id~ n
⟪ ts ∘ us ⟫ʰ    = ⟪ ts ⟫ʰ ⋆ ⟪ us ⟫ʰ
⟪ p n ⟫ʰ        = p~ n
⟪ <> ⟫ʰ         = []
⟪ < ts , t > ⟫ʰ = ⟪ ts ⟫ʰ ∙ ⟪ t ⟫

---------------------------------------------------------------------------------------------------
-- Proofs that the translation functions are inverses of each other

-- A scope safe term mapped to the cwf world returns the same

ws∘cwf : ∀ {n} (t : Tm-λ n) → t ~ ⟪ ⟦ t ⟧ ⟫

-- A cwf term mapped to a scope safe term returns the same

cwf∘ws : ∀ {n} (t : Tm-cwf n) → t ~ₜ ⟦ ⟪ t ⟫ ⟧

-- A Hom turned into a substitution and back returns the same

hom∘sub : ∀ {m n} (h : Hom m n) → h ~ₕ ⟦ ⟪ h ⟫ʰ ⟧ˢ

p1p'~ : ∀ m n → p1 m n ~ₕ ⟦ p′~ m n ⟧ˢ
p1p'~ m zero rewrite p′0=[] {m} = hom0~<> (p1 m zero)
p1p'~ m (suc n) = begin
  p1 m (suc n) ≈⟨ eta $ p1 m (suc n) ⟩
  < p n ∘ p1 m (suc n) , q `[ p1 m (suc n) ] > ≈⟨ cong~ₕ (λ x → < p n ∘ x , q `[ p1 m (1 + n) ] >) (p1=p2 m _) ⟩
  < p n ∘ p2 m (suc n) , q `[ p1 m (suc n) ] > ≈⟨ {!p2 (suc m) n!} ⟩
  ⟦ p′~ m (suc n) ⟧ˢ ∎
  where open EqR (HomS {_} {_})

p~⟦p⟧ : ∀ n → p n ~ₕ ⟦ p~ n ⟧ˢ
p~⟦p⟧ n = begin
  p n               ≈⟨ sym~ₕ (idL (p n)) ⟩
  id n ∘ p n        ≈⟨ p1p'~ 1 n ⟩
  ⟦ id~ n ⋆ p~ n ⟧ˢ ≈⟨ help ⟩
  ⟦ p~ n ⟧ˢ         ∎
  where open EqR (HomS {_} {_})
        help : ⟦ id~ n ⋆ p~ n ⟧ˢ ~ₕ ⟦ p~ n ⟧ˢ
        help rewrite ∘-lid (p~ n) = refl~ₕ

-- Interpreting a composition distributes

postulate ⟦⟧-∘-distₚ : ∀ {m n k} (σ : Subst n k) (γ : Subst m n) → ⟦ σ ⋆ γ ⟧ˢ ~ₕ ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ

⟦⟧-∘-dist : ∀ {m n k} (σ : Subst n k) (γ : Subst m n) → ⟦ σ ⋆ γ ⟧ˢ ~ₕ ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ

-- Interpreting a substitution commutes

[]-comm : ∀ {m n} (t : Tm-λ n) (σ : Subst m n) → ⟦ t [ σ ] ⟧ ~ₜ ⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]

[]-comm (var zero)    (x ∷ σ) = qCons ⟦ x ⟧ ⟦ σ ⟧ˢ
[]-comm (var (suc ι)) (x ∷ σ) = sym~ₜ $ begin
  ⟦ var ι ⟧ `[ p _ ] `[ < ⟦ σ ⟧ˢ , ⟦ x ⟧ > ] ≈⟨ sym~ₜ (clos ⟦ var ι ⟧ (p _) < ⟦ σ ⟧ˢ , ⟦ x ⟧ >) ⟩
  ⟦ var ι ⟧ `[ p _ ∘ < ⟦ σ ⟧ˢ , ⟦ x ⟧ > ]    ≈⟨ sym~ₜ (congh~ₜ (_`[_] ⟦ var ι ⟧) (pCons ⟦ x ⟧ ⟦ σ ⟧ˢ)) ⟩
  ⟦ var ι ⟧ `[ ⟦ σ ⟧ˢ ]                      ≈⟨ sym~ₜ ([]-comm (var ι) σ) ⟩
  ⟦ lookup ι σ ⟧                             ∎
  where open EqR (TermS {_})

[]-comm (t · u) σ = begin
  app ⟦ t [ σ ] ⟧ ⟦ u [ σ ] ⟧                  ≈⟨ cong~ₜ (flip app ⟦ u [ σ ] ⟧) ([]-comm t σ) ⟩
  app (⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]) (⟦ u [ σ ] ⟧)        ≈⟨ cong~ₜ (app (⟦ t ⟧ `[ ⟦ σ ⟧ˢ ])) ([]-comm u σ) ⟩
  app (⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]) (⟦ u ⟧ `[ ⟦ σ ⟧ˢ ])  ≈⟨ appCm ⟦ t ⟧ ⟦ u ⟧ ⟦ σ ⟧ˢ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ `[ ⟦ σ ⟧ˢ ]                  ∎
  where open EqR (TermS {_})

[]-comm (ƛ t) σ = begin
  lam ⟦ t [ ↑ₛ σ ] ⟧                          ≈⟨ cong~ₜ lam ([]-comm t (↑ₛ σ)) ⟩
  lam (⟦ t ⟧ `[ < ⟦ map weaken~ σ ⟧ˢ , q > ]) ≈⟨ congh~ₜ (λ x → lam (⟦ t ⟧ `[ x ])) help ⟩
  lam (⟦ t ⟧ `[ < ⟦ σ ⋆ p~ _ ⟧ˢ , q > ])      ≈⟨ congh~ₜ (λ x → lam (⟦ t ⟧ `[ < x , q > ])) (⟦⟧-∘-distₚ σ (p~ _)) ⟩
  lam (⟦ t ⟧ `[ < ⟦ σ ⟧ˢ ∘ ⟦ p~ _ ⟧ˢ , q > ]) ≈⟨ congh~ₜ (λ x → lam (⟦ t ⟧ `[ < ⟦ σ ⟧ˢ ∘ x , q > ]))
                                                         (sym~ₕ (p~⟦p⟧ _)) ⟩
  lam (⟦ t ⟧ `[ < ⟦ σ ⟧ˢ ∘ p _ , q > ])       ≈⟨ sym~ₜ (lamCm ⟦ t ⟧ ⟦ σ ⟧ˢ) ⟩
  lam ⟦ t ⟧ `[ ⟦ σ ⟧ˢ ]                       ∎
  where open EqR (TermS {_})
        help : < ⟦ map weaken~ σ ⟧ˢ , q > ~ₕ < ⟦ σ ⋆ p~ _ ⟧ˢ , q >
        help rewrite sym (mapWk-⋆p σ) = refl~ₕ

⟦⟧-∘-dist [] γ = sym~ₕ (∘<> ⟦ γ ⟧ˢ)
⟦⟧-∘-dist (t ∷ σ) γ = begin
  < ⟦ σ ⋆ γ ⟧ˢ , ⟦ t [ γ ] ⟧ >            ≈⟨ cong~ₕ (λ z → < z , _ >) (⟦⟧-∘-dist σ γ) ⟩
  < ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ , ⟦ t [ γ ] ⟧ >       ≈⟨ congt~ₕ (λ z → < _ , z >) ([]-comm t γ) ⟩
  < ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ , ⟦ t ⟧ `[ ⟦ γ ⟧ˢ ] > ≈⟨ sym~ₕ (maps ⟦ t ⟧ ⟦ σ ⟧ˢ ⟦ γ ⟧ˢ) ⟩
  < ⟦ σ ⟧ˢ , ⟦ t ⟧ > ∘ ⟦ γ ⟧ˢ             ∎
  where open EqR (HomS {_} {_})

-- t ∈ Tm-λ n ⇒ ⟪ ⟦ t ⟧ ⟫ ~ t
 
ws∘cwf (ƛ t) = ξ t ⟪ ⟦ t ⟧ ⟫ (ws∘cwf t)
ws∘cwf (t · u) = apcong (ws∘cwf t) (ws∘cwf u)
ws∘cwf (var zero) = refl~
ws∘cwf (var (suc i))
  rewrite sym $ lookup-p i
     = cong~ (λ x → x [ p~ _ ]) (ws∘cwf (var i))

-- t ∈ Tm-cwf n ⇒ ⟦ ⟪ t ⟫ ⟧ ~ t

cwf∘ws q = refl~ₜ
cwf∘ws (lam t) = cong~ₜ lam (cwf∘ws t)
cwf∘ws (app t u) = trans~ₜ (cong~ₜ (app t) (cwf∘ws u)) (cong~ₜ (λ z → app z _) (cwf∘ws t))
cwf∘ws (t `[ us ]) = sym~ₜ $ begin
  ⟦ ⟪ t ⟫ [ ⟪ us ⟫ʰ ] ⟧         ≈⟨ []-comm ⟪ t ⟫ ⟪ us ⟫ʰ ⟩
  ⟦ ⟪ t ⟫ ⟧ `[ ⟦ ⟪ us ⟫ʰ ⟧ˢ ]   ≈⟨ sym~ₜ (cong~ₜ (_`[ ⟦ ⟪ us ⟫ʰ ⟧ˢ ]) (cwf∘ws t)) ⟩
  t `[ ⟦ ⟪ us ⟫ʰ ⟧ˢ ]           ≈⟨ sym~ₜ (congh~ₜ (t `[_]) (hom∘sub us)) ⟩
  t `[ us ]                     ∎
  where open EqR (TermS {_})

-- h ∈ Hom m n ⇒ ⟦ ⟪ h ⟫ ⟧ ~ h

hom∘sub (id zero) = id₀
hom∘sub (id (suc m)) = begin
  id (1 + m)                  ≈⟨ varp {m} ⟩
  < p m , q >                 ≈⟨ cong~ₕ (<_, q >) (hom∘sub (p m)) ⟩
  < ⟦ p~ m ⟧ˢ , q >           ∎
  where open EqR (HomS {_} {_})

hom∘sub (h ∘ g) = sym~ₕ $ begin
  ⟦ ⟪ h ⟫ʰ ⋆ ⟪ g ⟫ʰ ⟧ˢ          ≈⟨ ⟦⟧-∘-dist ⟪ h ⟫ʰ ⟪ g ⟫ʰ ⟩
  ⟦ ⟪ h ⟫ʰ ⟧ˢ ∘ ⟦ ⟪ g ⟫ʰ ⟧ˢ     ≈⟨ sym~ₕ (cong~ₕ (_∘ ⟦ ⟪ g ⟫ʰ ⟧ˢ) (hom∘sub h)) ⟩
  h ∘ ⟦ ⟪ g ⟫ʰ ⟧ˢ               ≈⟨ sym~ₕ (cong~ₕ (_∘_ h) (hom∘sub g)) ⟩
  h ∘ g                         ∎
  where open EqR (HomS {_} {_})
 
hom∘sub (p n) = p~⟦p⟧ n

hom∘sub <> = refl~ₕ
hom∘sub < h , x > = begin
  < h , x >                     ≈⟨ cong~ₕ (<_, x >) (hom∘sub h) ⟩
  < ⟦ ⟪ h ⟫ʰ ⟧ˢ , x >           ≈⟨ congt~ₕ (λ z → < _ , z >) (cwf∘ws x) ⟩
  < ⟦ ⟪ h ⟫ʰ ⟧ˢ , ⟦ ⟪ x ⟫ ⟧ >   ∎
  where open EqR (HomS {_} {_})
