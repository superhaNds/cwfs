-------------------------------------------------------------------------
-- Simply typed category with families as a generalized algebraic
-- theory using directly typed well-scoped terms. It is implemented with
-- explicit substitutions. This is a scwf by construction and in extension
-- a λβη-scwf.
-------------------------------------------------------------------------
module SimpTyped.ExpSubLam where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec hiding ([_])
open import Relation.Binary using (IsEquivalence ; Setoid)

open import SimpTyped.Type
open import SimpTyped.Scwf

-------------------------------------------------------------------------
-- Terms and substitutions as mutually recursive data types

data Tm  : ∀ {n}   → Ctx n → Ty    → Set
data Sub : ∀ {n m} → Ctx n → Ctx m → Set

data Tm where

  q : ∀ {n A} {Γ : Ctx n} → Tm (Γ ∙ A) A

  _[_] : ∀ {m n A} {Γ : Ctx n} {Δ : Ctx m}
         → Tm Γ A
         → Sub Δ Γ
         → Tm Δ A
  
  app : ∀ {n A B} {Γ : Ctx n}
        → Tm Γ (A ⇒ B)
        → Tm Γ A
        → Tm Γ B
  
  lam : ∀ {n A B} {Γ : Ctx n}
        → Tm (Γ ∙ A) B
        → Tm Γ (A ⇒ B)
         
data Sub where

  <> : ∀ {n} {Γ : Ctx n} → Sub Γ ⋄
  
  id : ∀ {n} {Γ : Ctx n} → Sub Γ Γ
  
  p : ∀ {n A} {Γ : Ctx n} → Sub (Γ ∙ A) Γ
  
  _∘_ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
        → Sub Γ Θ
        → Sub Δ Γ
        → Sub Δ Θ
                                     
  <_,_> : ∀ {m n A} {Γ : Ctx n} {Δ : Ctx m}
          → Sub Δ Γ
          → Tm Δ A
          → Sub Δ (Γ ∙ A)
          
infix 6 _~_
infix 6 _≈_

data _~_ : ∀ {n A} {Γ : Ctx n} (t₁ t₂ : Tm Γ A)              → Set
data _≈_ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (γ₁ γ₂ : Sub Γ Δ) → Set

data _~_ where

  subId : ∀ {n A} {Γ : Ctx n} {t : Tm Γ A} → t [ id ] ~ t
          
  qCons : ∀ {m n A} {Γ : Ctx n} {Δ : Ctx m} {t : Tm Δ A} {γ : Sub Δ Γ}
          → q [ < γ , t > ] ~ t
         
  subComp : ∀ {m n k A} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
              (t : Tm Θ A) {γ : Sub Γ Θ} {δ : Sub Δ Γ}
            → t [ γ ∘ δ ] ~ t [ γ ] [ δ ]

  subApp : ∀ {m n A B} {Γ : Ctx n} {Δ : Ctx m}
            {t : Tm Γ (A ⇒ B)} {u : Tm Γ A} {γ : Sub Δ Γ}
           → app (t [ γ ]) (u [ γ ]) ~ app t u [ γ ]

  subLam : ∀ {m n A B} {Γ : Ctx n} {Δ : Ctx m}
            {t : Tm (Γ ∙ A) B} {γ  : Sub Δ Γ}
           → lam t [ γ ] ~ lam (t [ < γ ∘ p , q > ])

  beta : ∀ {n A B} {Γ : Ctx n} {t : Tm (Γ ∙ A) B} {u}
         → app (lam t) u ~ t [ < id , u > ]
        
  eta : ∀ {n A B} {Γ : Ctx n} {t : Tm Γ (A ⇒ B)}
        → lam (app (t [ p ]) q) ~ t
         
  cong-sub : ∀ {m n A} {Γ : Ctx n} {Δ : Ctx m}
              {t t' : Tm Γ A} {γ γ' : Sub Δ Γ}
             → t ~ t'
             → γ ≈ γ'
             → t [ γ ] ~ t' [ γ' ]
            
  cong-app : ∀ {n A B} {Γ : Ctx n}
               {t u : Tm Γ (A ⇒ B)} {t' u' : Tm Γ A}
             → t ~ u
             → t' ~ u'
             → app t t' ~ app u u'
             
  cong-lam : ∀ {n A B} {Γ : Ctx n} {t t' : Tm (Γ ∙ A) B}
             → t ~ t'
             → lam t ~ lam t'
             
  sym~ : ∀ {n A} {Γ : Ctx n} {t t' : Tm Γ A}
         → t ~ t'
         → t' ~ t
         
  trans~ : ∀ {n A} {Γ : Ctx n} {t t' t'' : Tm Γ A}
           → t ~ t'
           → t' ~ t''
           → t ~ t''
  
data _≈_ where

  id-zero : id {Γ = ⋄} ≈ <>
  
  left-zero : ∀ {m n}
                {Γ : Ctx n} {Δ : Ctx m}
                {γ : Sub Γ Δ}
              → <> ∘ γ ≈ <>
  
  idExt : ∀ {n A} {Γ : Ctx n} → id {Γ = Γ ∙ A} ≈ < p , q >
  
  idL  : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ : Sub Γ Δ}
         → id ∘ γ ≈ γ
  
  idR  : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ : Sub Δ Γ}
         → γ ∘ id ≈ γ

  assoc : ∀ {m n k l} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {Λ : Ctx l} →
           (γ : Sub Γ Θ) (δ : Sub Δ Γ) (τ : Sub Λ Δ)
          → (γ ∘ δ) ∘ τ ≈ γ ∘ (δ ∘ τ)
         
  pCons : ∀ {m n A} {Γ : Ctx n} {Δ : Ctx m} {t : Tm Δ A} (γ : Sub Δ Γ)
          → p ∘ < γ , t > ≈ γ
          
  compExt : ∀ {m n k A} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
              {t : Tm Δ A} {γ : Sub Δ Θ} {δ : Sub Γ Δ}
            → < γ , t > ∘ δ ≈ < γ ∘ δ , t [ δ ] >
         
  cong-<,> : ∀ {m n A} {Γ : Ctx n} {Δ : Ctx m} {t t' : Tm Γ A} {γ γ' : Sub Γ Δ}
             → t ~ t'
             → γ ≈ γ'
             → < γ , t > ≈ < γ' , t' >
            
  cong-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
             {γ δ : Sub Δ Θ} {γ' δ' : Sub Γ Δ}
           → γ ≈ δ
           → γ' ≈ δ'
           → γ ∘ γ' ≈ δ ∘ δ'
           
  sym≈ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ γ' : Sub Δ Γ}
         → γ ≈ γ'
         → γ' ≈ γ
  
  trans≈ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ γ' γ'' : Sub Δ Γ}
           → γ ≈ γ'
           → γ' ≈ γ''
           → γ ≈ γ''

refl~ : ∀ {n A} {Γ : Ctx n} {t : Tm Γ A} → t ~ t
refl~ = trans~ (sym~ subId) subId

refl≈ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {γ : Sub Δ Γ} → γ ≈ γ
refl≈ = trans≈ (sym≈ idL) idL

IsEquiv~ : ∀ {n A} {Γ : Ctx n} → IsEquivalence (_~_ {A = A} {Γ})
IsEquiv~ = record { refl = refl~ ; sym = sym~ ; trans = trans~ }

IsEquiv≈ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → IsEquivalence (_≈_ {Γ = Γ} {Δ})
IsEquiv≈ = record { refl = refl≈ ; sym = sym≈ ; trans = trans≈ }

TmSetoid : ∀ {n A} {Γ : Ctx n} → Setoid _ _
TmSetoid {n} {A} {Γ} = record
  { Carrier = Tm Γ A
  ; _≈_ = _~_
  ; isEquivalence = IsEquiv~
  }

SubSetoid : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → Setoid _ _
SubSetoid {Δ = Δ} {Γ} = record
  { Carrier = Sub Δ Γ
  ; _≈_ = _≈_
  ; isEquivalence = IsEquiv≈
  }


{-
ExpSubScwf : Scwf
ExpSubScwf = record
               { Ty = Ty
               ; Ctx = Ctx
               ; Tm = Tm
               ; Sub = Sub
               ; ⋄ = ⋄
               ; _∙_ = _∙_
               ; _~_ = _~_
               ; _≈_ = _≈_
               ; IsEquiv~ = IsEquiv~
               ; IsEquiv≈ = IsEquiv≈
               ; id = id
               ; _∘_ = _∘_
               ; _[_] = _[_]
               ; <> = <>
               ; <_,_> = <_,_>
               ; p = p
               ; q = q
               ; id-zero = id-zero
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


-}
