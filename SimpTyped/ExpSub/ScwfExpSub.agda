-------------------------------------------------------------------------------
-- The straightfoward term model for a Scwf where everything is explicit
-- It is the initial object in the category of scwfs
-------------------------------------------------------------------------------
module SimpTyped.ExpSub.ScwfExpSub where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec hiding ([_] ; _∈_)
open import Data.Fin
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (IsEquivalence ; Setoid)
import Relation.Binary.EqReasoning as EqR
open import SimpTyped.Context
open import SimpTyped.Type
open import SimpTyped.Scwf

-------------------------------------------------------------------------------
-- Terms and Substitutions

data Tm : Ctx → Ty → Set
data Sub : Ctx → Ctx → Set

-- Terms

data Tm where

  -- zeroth variable
  
  q : ∀ {Γ α} → Tm (Γ ∙ α) α

  -- explicit substitution
  
  _[_] : ∀ {Γ Δ α} → Tm Γ α  → Sub Δ Γ → Tm Δ α

  -- λ abstraction

  lam : ∀ {Γ α β} → Tm (Γ ∙ α) β → Tm Γ (α ⇒ β)

  -- function application
 
  app : ∀ {Γ α β} → Tm Γ (α ⇒ β) → Tm Γ α → Tm Γ β

-- Substitutions

infix 8 _∘_

data Sub where

  id : ∀ {Γ} → Sub Γ Γ
  
  _∘_ : ∀ {Γ Δ Θ} → Sub Γ Θ → Sub Δ Γ → Sub Δ Θ

  <> : ∀ {Γ} → Sub Γ ε

  <_,_> : ∀ {Γ Δ α} → Sub Γ Δ → Tm Γ α  → Sub Γ (Δ ∙ α)

  p : ∀ {Γ α} → Sub (Γ ∙ α) Γ

-- weakening of a single term

weaken-same : ∀ {Γ α} → Tm Γ α → Tm (Γ ∙ α) α
weaken-same = _[ p ]

infix 4 _≈_
infix 4 _≋_

-- Equality for terms and substitutions with introduction rules for the axioms

data _≈_  : ∀ {Γ α} (t₁ t₂ : Tm Γ α) → Set
data _≋_ : ∀ {Γ Δ} (γ₁ γ₂ : Sub Γ Δ) → Set

data _≈_ where

  subId : ∀ {Γ α} (t : Tm Γ α) → t [ id ] ≈ t

  qCons : ∀ {Γ Δ α} (t : Tm Γ α) (γ : Sub Γ Δ) → q [ < γ , t > ] ≈ t

  subComp : ∀ {Γ Δ Θ α} (t : Tm Δ α) (γ : Sub Γ Δ) (δ : Sub Θ Γ)
            → t [ γ ∘ δ ] ≈ t [ γ ] [ δ ]
             
  subApp : ∀ {Γ Δ α β} (t : Tm Γ (α ⇒ β)) (u : Tm Γ α) (γ : Sub Δ Γ)
           → app (t [ γ ]) (u [ γ ]) ≈ app t u [ γ ]
             
  subLam : ∀ {Γ Δ α β} (t : Tm (Γ ∙ α) β) (γ : Sub Δ Γ)
           → lam t [ γ ] ≈ lam (t [ < γ ∘ p , q > ])

  -- beta and eta equality

  β : ∀ {Γ α β} {t : Tm (Γ ∙ α) β} {u} → app (lam t) u ≈ t [ < id , u > ] 

  η : ∀ {Γ α β} {t : Tm Γ (α ⇒ β)} → lam (app (t [ p ]) q) ≈ t

  cong-sub : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Sub Δ Γ}
             → t ≈ t'
             → γ ≋ γ'
             → t [ γ ] ≈ t' [ γ' ]
             
  cong-app : ∀ {Γ α β} {t t' : Tm Γ (α ⇒ β)} {u u' : Tm Γ α}
             → t ≈ t'
             → u ≈ u'
             → app t u ≈ app t' u'
               
  cong-lam : ∀ {Γ α β} {t t' : Tm (Γ ∙ α) β}
             → t ≈ t'
             → lam t ≈ lam t'
             
  sym≈ : ∀ {Γ α} {t t' : Tm Γ α}
         → t ≈ t'
         → t' ≈ t
             
  trans≈ : ∀ {Γ α} {t t' t'' : Tm Γ α}
           → t ≈ t'
           → t' ≈ t''
           → t ≈ t''

data _≋_ where

  -- identity of zero length is the empty substitution

  id₀ : id {ε} ≋ <>

  -- the empty substitution is a left zero in composition

  left-zero : ∀ {Γ Δ} (γ : Sub Γ Δ) → <> ∘ γ ≋ <>

  -- p with q is the extended identity

  idExt : ∀ {Γ α} → id {Γ ∙ α} ≋ < p , q >

  -- category of substitutions

  idL : ∀ {Γ Δ} (γ : Sub Δ Γ) → id ∘ γ ≋ γ
              
  idR : ∀ {Γ Δ} (γ : Sub Γ Δ) →  γ ∘ id ≋ γ
              
  assoc : ∀ {Γ Δ Θ Λ} (γ : Sub Δ Θ) (δ : Sub Γ Δ) (ζ : Sub Λ Γ)
          → (γ ∘ δ) ∘ ζ ≋ γ ∘ (δ ∘ ζ)

  -- p is the first projection

  pCons : ∀ {Δ Θ α} (t : Tm Δ α) (γ : Sub Δ Θ) → p ∘ < γ , t > ≋ γ

  -- composition with extended substitution 

  compExt : ∀ {Γ Δ Θ α} (t : Tm Δ α) (γ : Sub Δ Θ) (δ : Sub Γ Δ)
            → < γ , t > ∘ δ ≋ < γ ∘ δ , t [ δ ] >

  -- congruence

  cong-<,> : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Sub Γ Δ}
             → t ≈ t'
             → γ ≋ γ'
             → < γ , t > ≋ < γ' , t' >
              
  cong-∘ : ∀ {Γ Δ Θ} {γ δ : Sub Δ Θ} {γ' δ' : Sub Γ Δ}
           → γ ≋ δ
           → γ' ≋ δ'
           → γ ∘ γ' ≋ δ ∘ δ'
             
  sym≋ : ∀ {Γ Δ} {γ γ' : Sub Γ Δ}
         → γ ≋ γ'
         → γ' ≋ γ
              
  trans≋ : ∀ {Γ Δ} {γ γ' γ'' : Sub Γ Δ}
           → γ ≋ γ'
           → γ' ≋ γ''
           → γ ≋ γ''

-- The relations as setoids

refl≈ : ∀ {Γ α} {t : Tm Γ α} → t ≈ t
refl≈ {t = t} = trans≈ (sym≈ (subId t)) (subId t) 

≈equivr : ∀ {Γ α} → IsEquivalence (_≈_ {Γ} {α})
≈equivr = record
  { refl = refl≈
  ; sym = sym≈
  ; trans = trans≈
  }

TmSetoid : ∀ {Γ α} → Setoid _ _
TmSetoid {Γ} {α} = record
  { Carrier = Tm Γ α
  ; _≈_ = _≈_
  ; isEquivalence = ≈equivr
  }

refl≋ : ∀ {Γ Δ} {γ : Sub Γ Δ} → γ ≋ γ
refl≋ {γ = γ} = trans≋ (sym≋ (idL γ)) (idL γ)

≋equivr : ∀ {Γ Δ} → IsEquivalence (_≋_ {Γ} {Δ})
≋equivr = record
  { refl = refl≋
  ; sym = sym≋
  ; trans = trans≋
  }

SubSetoid : ∀ {Γ Δ} → Setoid _ _
SubSetoid {Γ} {Δ} = record
  { Carrier = Sub Γ Δ
  ; _≈_ = _≋_
  ; isEquivalence = ≋equivr
  }

cong-sub₁ : ∀ {Γ Δ α} {t₁ t₂ : Tm Γ α} {γ : Sub Δ Γ}
            → t₁ ≈ t₂
            → t₁ [ γ ] ≈ t₂ [ γ ]
cong-sub₁ eq = cong-sub eq refl≋

cong-sub₂ : ∀ {Γ Δ α} {t : Tm Γ α} {γ₁ γ₂ : Sub Δ Γ}
            → γ₁ ≋ γ₂
            → t [ γ₁ ] ≈ t [ γ₂ ]
cong-sub₂ = cong-sub refl≈

cong-∘₁ : ∀ {Δ Γ Ξ} {γ₁ γ₂ : Sub Δ Γ} {δ : Sub Ξ Δ}
          → γ₁ ≋ γ₂
          → γ₁ ∘ δ ≋ γ₂ ∘ δ
cong-∘₁ eq = cong-∘ eq refl≋

cong-∘₂ : ∀ {Δ Γ Ξ} {γ₁ γ₂ : Sub Ξ Δ} {δ : Sub Δ Γ}
          → γ₁ ≋ γ₂
          → δ ∘ γ₁ ≋ δ ∘ γ₂
cong-∘₂ = cong-∘ refl≋ 

cong-<, : ∀ {Δ Γ α} {γ₁ γ₂ : Sub Δ Γ} {t : Tm Δ α}
          → γ₁ ≋ γ₂
          → < γ₁ , t > ≋ < γ₂ , t >
cong-<, = cong-<,> refl≈           

cong-,> : ∀ {Δ Γ α} {γ : Sub Δ Γ} {t u : Tm Δ α}
          → t ≈ u
          → < γ , t > ≋ < γ , u >
cong-,> eq = cong-<,> eq refl≋ 

-------------------------------------------------------------------------------
-- A couple of theorems using the axiomatization

-- Every substitution

ter-arrow : ∀ {Γ} (γ : Sub Γ ε) → γ ≋ <>
ter-arrow γ = begin
  γ
    ≈⟨ sym≋ (idL γ) ⟩
  id {ε} ∘ γ
    ≈⟨ cong-∘₁ id₀ ⟩
  <> ∘ γ
    ≈⟨ left-zero γ ⟩
  <>
    ∎
  where open EqR (SubSetoid {_} {_})

-- Surjective pairing

surj-<,> : ∀ {Γ Δ α} (γ : Sub Γ (Δ ∙ α)) → γ ≋ < p ∘ γ , q [ γ ] >
surj-<,> γ = begin
  γ
    ≈⟨ sym≋ (idL γ) ⟩
  id ∘ γ
    ≈⟨ cong-∘₁ idExt ⟩
  < p , q > ∘ γ
    ≈⟨ compExt q p γ ⟩
  < p ∘ γ , q [ γ ] >
    ∎
  where open EqR (SubSetoid {_} {_})

Tm-Scwf : Scwf
Tm-Scwf = record
            { Ty = Ty
            ; Ctx = Ctx
            ; Tm = Tm
            ; Sub = Sub
            ; ⋄ = ε
            ; _∙_ = _∙_
            ; _≈_ = _≈_
            ; _≋_ = _≋_
            ; IsEquivT = ≈equivr
            ; IsEquivS = ≋equivr
            ; id = id
            ; _∘_ = _∘_
            ; _[_] = _[_]
            ; <> = <>
            ; <_,_> = <_,_>
            ; p = p
            ; q = q
            ; id₀ = id₀
            ; left-zero = left-zero
            ; idExt = idExt
            ; idL = idL
            ; idR = idR
            ; assoc = assoc
            ; subId = subId
            ; pCons = pCons
            ; qCons = qCons
            ; subComp = subComp
            ; compExt = compExt
            ; cong-sub = cong-sub
            ; cong-<,> = cong-<,>
            ; cong-∘ = cong-∘
            }

Tm-λ-scwf : Lambda-scwf
Tm-λ-scwf = record
              { scwf = Tm-Scwf
              ; _`→_ = _⇒_
              ; lam = lam
              ; app = app
              ; subApp = subApp
              ; subLam = subLam
              ; cong-lam = cong-lam
              ; cong-app = cong-app
              }

Tm-λ-βη-scwf : Lambda-βη-scwf
Tm-λ-βη-scwf = record
                 { lambda-scwf = Tm-λ-scwf
                 ; β = β
                 ; η = η
                 }
