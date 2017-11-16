-------------------------------------------------------------------------------
-- Proofs of the equational laws of a ucwf and a λβ-ucwf for the wellscoped
-- terms.
-------------------------------------------------------------------------------

module Unityped.Wellscoped.WsUcwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function as Fun using (_∘_ ; _$_ ; flip ; const)
open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Unityped.Ucwf
open import Unityped.Wellscoped.Properties
open import Unityped.Wellscoped.Syntax
open import Unityped.Wellscoped.Substitution
open import Unityped.Wellscoped.Beta
import Relation.Binary.EqReasoning as EqR

-------------------------------------------------------------------------------
-- Term is a Ucwf

-- id = < p , q >

id=pq : ∀ {n} → id {1 + n} ≡ p ∙ q
id=pq = refl

-- Substituting in the identity gives the same term

t[id] : ∀ {n} (t : Term n) → t [ id ] ≡ t
t[id] (var i) = lookup-id i
t[id] (t · u) = trans (cong (_· u [ id ]) (t[id] t))
                      (cong (_·_ t) (t[id] u))
t[id] (ƛ t) = begin
  ƛ (t [ ↑ₛ id ])   ≡⟨⟩
  ƛ (t [ p' ∙ q ])  ≡⟨ cong (λ x → ƛ (t [ x ∙ q ])) (sym p=p') ⟩
  ƛ (t [ p ∙ q ])   ≡⟨ cong (ƛ ∘ t [_]) (sym id=pq) ⟩
  ƛ (t [ id ])      ≡⟨ cong ƛ (t[id] t) ⟩
  ƛ t               ∎
  where open P.≡-Reasoning

{-t[id]~ : ∀ {n} (t : Term n) → t [ id ] ~ t
t[id]~ (var i) rewrite lookup-id i = varcong i
t[id]~ (t · u) = apcong (t[id]~ t) (t[id]~ u)
t[id]~ (ƛ t) = begin
  ƛ (t [ ↑ₛ id ])  ≈⟨ refl~ ⟩
  ƛ (t [ p' ∙ q ]) ≈⟨ cong≡~ (λ x → ƛ (t [ x ∙ q ])) (sym p=p') ⟩
  ƛ (t [ p ∙ q ])  ≈⟨ ξ (t[id]~ t) ⟩
  ƛ t              ∎
  where open EqR (TermSetoid {_})-}
  
-- Substituting in a composition is applying the substitution to the first and then the second

[]-asso : ∀ {m n k} (t : Term n) (ρ : Subst m n) (σ : Subst k m) →
          t [ ρ ⋆ σ ] ≡ t [ ρ ] [ σ ]
[]-asso (var ()) [] σ 
[]-asso (var zero) (x ∷ ρ) σ = refl
[]-asso (var (suc i)) (x ∷ ρ) σ = []-asso (var i) ρ σ
[]-asso (t · u) ρ σ = cong₂ _·_ ([]-asso t ρ σ) ([]-asso u ρ σ)
[]-asso (ƛ t) ρ σ = trans (cong (ƛ ∘ t [_]) (↑ₛ-dist ρ σ))
                            (cong ƛ ([]-asso t (↑ₛ ρ) (↑ₛ σ)))

{-[]-asso~ : ∀ {m n k} (t : Term n) (ρ : Subst m n) (σ : Subst k m) →
           t [ ρ ⋆ σ ] ~ t [ ρ ] [ σ ]
[]-asso~ (var zero) (x ∷ ρ) σ = refl~
[]-asso~ (var (suc i)) (x ∷ ρ) σ = []-asso~ (var i) ρ σ
[]-asso~ (t · u) ρ σ = apcong ([]-asso~ t ρ σ) ([]-asso~ u ρ σ)
[]-asso~ (ƛ t) ρ σ = trans~ (ξ (cong-[] {t = t} refl~ (↑ₛ-dist ρ σ)))
                            (ξ ([]-asso~ t (↑ₛ ρ) (↑ₛ σ)))-}

-- identity sub of zero

id₀[] : id {0} ≡ []
id₀[] = refl

-- the empty substitution is a left absorbing element (left zero)

∘-[] : ∀ {m n} (ρ : Subst m n) → [] ⋆ ρ ≡ []
∘-[] _ = refl

-- Composing with the projection substitution drops the last element

p⋆Cons : ∀ {n k} (t : Term n) (σ : Subst n k) → p ⋆ (σ ∙ t) ≡ σ
p⋆Cons t σ = trans (p∘-lookup (σ ∙ t)) (map-lookup-↑ (σ ∙ t))

-- Category of substitutions

-- Composing substitutions is associative

⋆-asso : ∀ {m n k j} (σ : Subst m n) (γ : Subst k m) (δ : Subst j k) →
         (σ ⋆ γ) ⋆ δ ≡ σ ⋆ (γ ⋆ δ)
⋆-asso [] γ δ = refl
⋆-asso (t ∷ σ) γ δ = sym $ begin
  (σ ∙ t) ⋆ (γ ⋆ δ)            ≡⟨⟩
  σ ⋆ (γ ⋆ δ) ∙ t [ γ ⋆ δ ]    ≡⟨ cong (λ x → x ∷ _) ([]-asso t γ δ) ⟩
  σ ⋆ (γ ⋆ δ) ∙ t [ γ ] [ δ ]  ≡⟨ sym $ cong (t [ γ ] [ δ ] ∷_) (⋆-asso σ γ δ) ⟩
  (σ ⋆ γ) ⋆ δ ∙ t [ γ ] [ δ ]  ∎
  where open P.≡-Reasoning

-- id is a left identity

∘-lid : ∀ {m n} (σ : Subst m n) → id ⋆ σ ≡ σ
∘-lid [] = refl
∘-lid (x ∷ σ) = begin
  id ⋆ (σ ∙ x)      ≡⟨ ⋆=⋆₂ id (σ ∙ x) ⟩
  p ⋆₂ (σ ∙ x) ∙ x  ≡⟨ cong (_∙ x) (sym $ ⋆=⋆₂ p (σ ∙ x)) ⟩
  p ⋆ (σ ∙ x) ∙ x   ≡⟨ cong (_∙ x) (p⋆Cons x σ) ⟩
  σ ∙ x             ∎
  where open P.≡-Reasoning

-- id is a right identity (the proofs differ as composition is not a symmetric)

∘-rid : ∀ {m n} (σ : Subst m n) → σ ⋆ id ≡ σ
∘-rid [] = refl
∘-rid (t ∷ σ)
  rewrite t[id] t
        | ∘-rid σ = refl

-- Substituting the De Bruijn zero variable takes the last assumption

q[] : ∀ {m n} (t : Term m) (σ : Subst m n) → q [ σ ∙ t ] ≡ t
q[] _ _ = refl

-- Composing with a cons (by definition)

maps : ∀ {m n} (t : Term n) (σ : Subst n m) (γ : Subst m n) →
       (σ ∙ t) ⋆ γ ≡ (σ ⋆ γ) ∙ t [ γ ]
maps t σ γ = refl

-- Congruence rules

congSub : ∀ {n m} {t t' : Term n} {ρ ρ' : Subst m n} → t ≡ t' → ρ ≡ ρ' → t [ ρ ] ≡ t' [ ρ' ]
congSub refl refl = refl

cong-∙ : ∀ {n m} {t t' : Term m} {ρ ρ' : Subst m n} → t ≡ t' → ρ ≡ ρ' → ρ ∙ t ≡ ρ' ∙ t'
cong-∙ refl refl = refl

cong-⋆ : ∀ {m n k} {ρ σ : Subst m n} {ρ' σ' : Subst k m} →
         ρ ≡ σ → ρ' ≡ σ' → ρ ⋆ ρ' ≡ σ ⋆ σ'
cong-⋆ refl refl = refl

cong-ƛ : ∀ {n} {t t' : Term (suc n)} → t ≡ t' → ƛ t ≡ ƛ t'
cong-ƛ refl = refl

cong-ap : ∀ {n} {t t' u u' : Term n} → t ≡ t' → u ≡ u' → t · u ≡ t' · u'
cong-ap refl refl = refl

----------------------------------------------------------------------------------
-- Terms form a pure ucwf

Tm-ucwf : Ucwf
Tm-ucwf = record
            { Term  = Term
            ; Hom   = Subst
            ; _~ₜ_  = _≡_
            ; _~ₕ_  = _≡_
            ; id    = id
            ; <>    = []
            ; p     = p
            ; q     = vr 0
            ; _∘_   = _⋆_
            ; _[_]  = _[_]
            ; <_,_> = _∙_
            ; id₀   = id₀[]
            ; ∘<>   = ∘-[]
            ; varp  = id=pq
            ; idL   = ∘-lid
            ; idR   = ∘-rid
            ; assoc = ⋆-asso
            ; terId = t[id]
            ; pCons = p⋆Cons
            ; qCons = q[]
            ; clos  = []-asso
            ; maps  = maps
            ; cong-<,> = cong-∙
            ; cong-[_] = congSub
            ; cong-∘   = cong-⋆
            }

------------------------------------------------------------------------------------
-- Term is also a Ucwf with lambda - application

abs : ∀ {n m} (t : Term (1 + n)) (σ : Subst m n) → ƛ t [ σ ] ≡ ƛ (t [ (σ ⋆ p) ∙ q ])
abs t σ = sym (cong (λ x → ƛ (t [ x ∙ q ])) (mapWk-⋆p σ))

appSub : ∀ {n m} (t u : Term n) (ρ : Subst m n) → t [ ρ ] · u [ ρ ] ≡ (t · u) [ ρ ]
appSub t u ρ = refl 

Tm-λ-ucwf : Lambda-ucwf
Tm-λ-ucwf = record { ucwf   = Tm-ucwf
                   ; ƛ      = ƛ
                   ; _·_    = _·_
                   ; cong-ƛ = cong-ƛ
                   ; cong-· = cong-ap
                   ; app    = appSub
                   ; abs    = abs
                   }
{-
η′ : ∀ {n} (t : Term n) → ƛ (t [ p ] · q) ~ t
η′ t = trans~ (cong≡~ (λ x → ƛ (x · q)) (sym $ wk-[p] t)) (η t) 


Tm-λβη-ucwf : Lambda-βη-ucwf
Tm-λβη-ucwf = record { lambda-ucwf = Tm-λ-ucwf
                     ; β   = β
                     ; η   = η′
                     }
-}
