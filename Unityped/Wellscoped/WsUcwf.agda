-------------------------------------------------------------------------------
-- Proofs of the equational laws of a ucwf and a λβ-ucwf for the wellscoped
-- terms.
-------------------------------------------------------------------------------

module Unityped.Wellscoped.WsUcwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function as F using (_$_ ; flip ; const)
open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Unityped.Ucwf
open import Unityped.Wellscoped.Properties
open import Unityped.Wellscoped.Syntax
open import Unityped.Wellscoped.Substitution
-- open import Unityped.Wellscoped.Beta
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR

-------------------------------------------------------------------------------
-- Tm is a Ucwf

-- id = < p , q >

idExt : ∀ {n} → id {1 + n} ≡ p , q
idExt = refl

-- Substituting in the identity gives the same term

subId : ∀ {n} (t : Tm n) → t [ id ] ≡ t
subId (var i) = lookup-id i
subId (t · u) = cong₂ _·_ (subId t) (subId u)
subId (ƛ t) = begin
  ƛ (t [ ↑ id ])    ≡⟨⟩
  ƛ (t [ p' , q ])  ≡⟨ cong (λ x → ƛ (t [ x , q ])) (sym p=p') ⟩
  ƛ (t [ p , q ])   ≡⟨ cong (ƛ F.∘ t [_]) (sym idExt) ⟩
  ƛ (t [ id ])      ≡⟨ cong ƛ (subId t) ⟩
  ƛ t               ∎
  where open P.≡-Reasoning

{-subId~ : ∀ {n} (t : Tm n) → t [ id ] ~ t
subId~ (var i) rewrite lookup-id i = varcong i
subId~ (t · u) = apcong (subId~ t) (subId~ u)
subId~ (ƛ t) = begin
  ƛ (t [ ↑ₛ id ])  ≈⟨ refl~ ⟩
  ƛ (t [ p' , q ]) ≈⟨ cong≡~ (λ x → ƛ (t [ x , q ])) (sym p=p') ⟩
  ƛ (t [ p , q ])  ≈⟨ ξ (subId~ t) ⟩
  ƛ t              ∎
  where open EqR (TmSetoid {_})-}
  
-- Substituting in a composition is applying the substitution to the first and then the second

subComp : ∀ {m n k} (t : Tm n) (ρ : Subst m n) (σ : Subst k m) →
          t [ ρ ∘ σ ] ≡ t [ ρ ] [ σ ]
subComp (var ()) [] σ 
subComp (var zero) (x ∷ ρ) σ = refl
subComp (var (suc i)) (x ∷ ρ) σ = subComp (var i) ρ σ
subComp (t · u) ρ σ = cong₂ _·_ (subComp t ρ σ) (subComp u ρ σ)
subComp (ƛ t) ρ σ = trans (cong (ƛ F.∘ t [_]) (↑-dist ρ σ))
                            (cong ƛ (subComp t (↑ ρ) (↑ σ)))

{-subComp~ : ∀ {m n k} (t : Tm n) (ρ : Subst m n) (σ : Subst k m) →
           t [ ρ ∘ σ ] ~ t [ ρ ] [ σ ]
subComp~ (var zero) (x ∷ ρ) σ = refl~
subComp~ (var (suc i)) (x ∷ ρ) σ = subComp~ (var i) ρ σ
subComp~ (t · u) ρ σ = apcong (subComp~ t ρ σ) (subComp~ u ρ σ)
subComp~ (ƛ t) ρ σ = trans~ (ξ (cong-[] {t = t} refl~ (↑-dist ρ σ)))
                            (ξ (subComp~ t (↑ ρ) (↑ σ)))-}

-- identity sub of zero

id₀ : id {0} ≡ []
id₀ = refl

-- the empty substitution is a left absorbing element (left zero)

[]Lzero : ∀ {m n} (ρ : Subst m n) → [] ∘ ρ ≡ []
[]Lzero _ = refl

-- Composing with the projection substitution drops the last element

pCons : ∀ {n k} (σ : Subst n k) t → p ∘ (σ , t) ≡ σ
pCons σ t = trans (p∘-lookup (σ , t)) (map-lookup-↑ (σ , t))

-- Category of substitutions

-- Composing substitutions is associative

assoc : ∀ {m n k j} (σ : Subst m n) (γ : Subst k m) (δ : Subst j k) →
         (σ ∘ γ) ∘ δ ≡ σ ∘ (γ ∘ δ)
assoc [] γ δ = refl
assoc (t ∷ σ) γ δ = sym $ begin
  (σ , t) ∘ (γ ∘ δ)            ≡⟨⟩
  σ ∘ (γ ∘ δ) , t [ γ ∘ δ ]    ≡⟨ cong (λ x → _ , x) (subComp t γ δ) ⟩
  σ ∘ (γ ∘ δ) , t [ γ ] [ δ ]  ≡⟨ sym (cong (_, t [ γ ] [ δ ]) (assoc σ γ δ)) ⟩
  (σ ∘ γ) ∘ δ , t [ γ ] [ δ ]  ∎
  where open P.≡-Reasoning

{- sym $ begin
  (σ , t) ∘ (γ ∘ δ)            ≡⟨⟩
  (σ ∘ (γ ∘ δ)) , (t [ γ ∘ δ ])    ≡⟨ cong (λ x → x ∷ _) (subComp t γ δ) ⟩
  (σ ∘ (γ ∘ δ)) , (t [ γ ] [ δ ])  ≡⟨ sym $ cong (t [ γ ] [ δ ] ∷_) (∘-asso σ γ δ) ⟩
  ((σ ∘ γ) ∘ δ) , (t [ γ ] [ δ ])  ∎
  where open P.≡-Reasoning -}

-- id is a left identity

idL : ∀ {m n} (σ : Subst m n) → id ∘ σ ≡ σ
idL [] = refl
idL (x ∷ σ) = begin
  id ∘ (σ , x)      ≡⟨ ∘=∘₂ id (σ , x) ⟩
  p ∘₂ (σ , x) , x  ≡⟨ cong (_, x) (sym $ ∘=∘₂ p (σ , x)) ⟩
  p ∘ (σ , x) , x   ≡⟨ cong (_, x) (pCons σ x) ⟩
  σ , x             ∎
  where open P.≡-Reasoning

-- id is a right identity (the proofs differ as composition is not a symmetric)

idR : ∀ {m n} (σ : Subst m n) → σ ∘ id ≡ σ
idR [] = refl
idR (t ∷ σ)
  rewrite subId t
        | idR σ = refl

-- Substituting the De Bruijn zero picks the last

qCons : ∀ {m n} (σ : Subst m n) t → q [ σ , t ] ≡ t
qCons _ _ = refl

-- Composing with a cons (by definition)

compExt : ∀ {m n} (σ : Subst n m) (γ : Subst m n) t →
           (σ , t) ∘ γ ≡ (σ ∘ γ) , t [ γ ]
compExt _ _ _ = refl

-- Congruence rules

congSub : ∀ {n m} {t t' : Tm n} {ρ ρ' : Subst m n} →
           t ≡ t' →
           ρ ≡ ρ' →
           t [ ρ ] ≡ t' [ ρ' ]
congSub refl refl = refl

cong-, : ∀ {n m} {t t' : Tm m} {ρ ρ' : Subst m n} →
          t ≡ t' →
          ρ ≡ ρ' →
          ρ , t ≡ ρ' , t'
cong-, refl refl = refl

cong-∘ : ∀ {m n k} {ρ σ : Subst m n} {ρ' σ' : Subst k m} →
          ρ ≡ σ →
          ρ' ≡ σ' →
          ρ ∘ ρ' ≡ σ ∘ σ'
cong-∘ refl refl = refl

cong-ƛ : ∀ {n} {t t' : Tm (suc n)} → t ≡ t' → ƛ t ≡ ƛ t'
cong-ƛ refl = refl

cong-ap : ∀ {n} {t t' u u' : Tm n} →
           t ≡ t' →
           u ≡ u' →
           t · u ≡ t' · u'
cong-ap refl refl = refl

----------------------------------------------------------------------------------
-- Tms form a pure ucwf

Tm-ucwf : Ucwf
Tm-ucwf = record
            { Tm = Tm
            ; Sub = Subst
            ; _≈_ = _≡_
            ; _≋_ = _≡_
            ; IsEquivT = isEquivalence
            ; IsEquivS = isEquivalence
            ; id = id
            ; _∘_ = _∘_
            ; _[_] = _[_]
            ; <> = []
            ; <_,_> = _,_
            ; p = p
            ; q = q
            ; id₀ = id₀
            ; <>Lzero = []Lzero
            ; idExt = idExt
            ; idL = idL
            ; idR = idR
            ; assoc = assoc
            ; subId = subId
            ; pCons = pCons
            ; qCons = qCons
            ; subComp = λ h g t → subComp t h g
            ; compExt = compExt
            ; cong-<,> = cong-,
            ; cong-sub = congSub
            ; cong-∘ = cong-∘
            }
 
------------------------------------------------------------------------------------
-- Tm is also a Ucwf with lambda - application

abs : ∀ {n m} (σ : Subst m n) t → ƛ t [ σ ] ≡ ƛ (t [ (σ ∘ p) , q ])
abs σ t = sym (cong (λ x → ƛ (t [ x , q ])) (mapWk-∘p σ))

appSub : ∀ {n m} (ρ : Subst m n) t u → t [ ρ ] · u [ ρ ] ≡ (t · u) [ ρ ]
appSub _ _ _ = refl 

Tm-λ-ucwf : Lambda-ucwf
Tm-λ-ucwf = record
              { ucwf = Tm-ucwf
              ; lam = ƛ
              ; app = _·_
              ; subApp = appSub
              ; subLam = abs
              ; cong-lam = cong-ƛ
              ; cong-app = cong₂ _·_
              }
                   
{-
η′ : ∀ {n} (t : Tm n) → ƛ (t [ p ] · q) ~ t
η′ t = trans~ (cong≡~ (λ x → ƛ (x · q)) (sym $ wk-[p] t)) (η t) 
-}
