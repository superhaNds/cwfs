-------------------------------------------------------------------------
-- Simply typed category with families as a generalized algebraic
-- theory using directly typed well-scoped terms.
-------------------------------------------------------------------------
module ExtSimpTyped.IntExpSubLam where

open import Data.Nat renaming (ℕ to Nat)
open import ExtSimpTyped.CtxType

-------------------------------------------------------------------------
-- Terms and substitutions as mutually recursive data types

data Tm  : ∀ {n}   → Ctx n → Ty    → Set
data Sub : ∀ {n m} → Ctx n → Ctx m → Set

data Tm where

  q : ∀ {n α} {Γ : Ctx n} → Tm (Γ ∙ α) α

  _[_] : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
         → Tm Γ α
         → Sub Δ Γ
         → Tm Δ α
  
  app : ∀ {n α β} {Γ : Ctx n}
        → Tm Γ (α ⇒ β)
        → Tm Γ α
        → Tm Γ β
  
  lam : ∀ {n α β} {Γ : Ctx n}
        → Tm (Γ ∙ α) β
        → Tm Γ (α ⇒ β)
         
data Sub where

  <> : ∀ {n} {Γ : Ctx n} → Sub Γ ε
  
  id : ∀ {n} {Γ : Ctx n} → Sub Γ Γ
  
  p : ∀ {n α} {Γ : Ctx n} → Sub (Γ ∙ α) Γ
  
  _∘_ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
        → Sub Γ Θ
        → Sub Δ Γ
        → Sub Δ Θ
                                     
  <_,_> : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
          → Sub Δ Γ
          → Tm Δ α
          → Sub Δ (Γ ∙ α)
          
infix 6 _~_
infix 6 _≈_

data _~_ : ∀ {n α} {Γ : Ctx n} (t₁ t₂ : Tm Γ α)              → Set
data _≈_ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (γ₁ γ₂ : Sub Γ Δ) → Set

data _~_ where

  subId : ∀ {n α} {Γ : Ctx n} (t : Tm Γ α) → t [ id ] ~ t
          
  qCons : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m} (t : Tm Δ α) (ρ : Sub Δ Γ)
          → q [ < ρ , t > ] ~ t
         
  subComp : ∀ {m n k α} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
              (t : Tm Θ α) (ρ : Sub Γ Θ) (σ : Sub Δ Γ)
            → t [ ρ ∘ σ ] ~ t [ ρ ] [ σ ]

  subApp : ∀ {m n α β} {Γ : Ctx n} {Δ : Ctx m}
            (t : Tm Γ (α ⇒ β)) (u : Tm Γ α) (ρ : Sub Δ Γ)
           → app (t [ ρ ]) (u [ ρ ]) ~ app t u [ ρ ]

  subLam : ∀ {m n α β} {Γ : Ctx n} {Δ : Ctx m}
            (t : Tm (Γ ∙ α) β) (ρ  : Sub Δ Γ)
           → lam t [ ρ ] ~ lam (t [ < ρ ∘ p , q > ])
         
  cong-sub : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
              {t t' : Tm Γ α} {ρ ρ' : Sub Δ Γ}
             → t ~ t'
             → ρ ≈ ρ'
             → t [ ρ ] ~ t' [ ρ' ]
            
  cong-app : ∀ {n α β} {Γ : Ctx n}
               {t u : Tm Γ (α ⇒ β)} {t' u' : Tm Γ α}
             → t ~ u
             → t' ~ u'
             → app t t' ~ app u u'
             
  cong-lam : ∀ {n α β} {Γ : Ctx n} {t t' : Tm (Γ ∙ α) β}
             → t ~ t'
             → lam t ~ lam t'
             
  sym~ : ∀ {n α} {Γ : Ctx n} {t t' : Tm Γ α}
         → t ~ t'
         → t' ~ t
         
  trans~ : ∀ {n α} {Γ : Ctx n} {t t' t'' : Tm Γ α}
           → t ~ t'
           → t' ~ t''
           → t ~ t''
  
data _≈_ where

  id-zero : id {Γ = ε} ≈ <>
  
  left-zero : ∀ {m n}
                {Γ : Ctx n} {Δ : Ctx m}
                (ρ : Sub Γ Δ)
              → <> ∘ ρ ≈ <>
  
  idExt : ∀ {n α} {Γ : Ctx n} → id {Γ = Γ ∙ α} ≈ < p , q >
  
  idL  : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Sub Γ Δ)
         → id ∘ ρ ≈ ρ
  
  idR  : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Sub Δ Γ)
         → ρ ∘ id ≈ ρ

  assoc : ∀ {m n k l} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {Λ : Ctx l} →
           (ρ : Sub Γ Θ) (σ : Sub Δ Γ) (τ : Sub Λ Δ)
          → (ρ ∘ σ) ∘ τ ≈ ρ ∘ (σ ∘ τ)
         
  pCons : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m} (t : Tm Δ α) (ρ : Sub Δ Γ)
          → p ∘ < ρ , t > ≈ ρ
          
  compExt : ∀ {m n k α} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
              (t : Tm Δ α) (ρ : Sub Δ Θ) (σ : Sub Γ Δ)
            → < ρ , t > ∘ σ ≈ < ρ ∘ σ , t [ σ ] >
         
  cong-<,> : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m} {t t' : Tm Γ α} {ρ ρ' : Sub Γ Δ}
             → t ~ t'
             → ρ ≈ ρ'
             → < ρ , t > ≈ < ρ' , t' >
            
  cong-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
             {ρ σ : Sub Δ Θ} {ρ' σ' : Sub Γ Δ}
           → ρ ≈ σ
           → ρ' ≈ σ'
           → ρ ∘ ρ' ≈ σ ∘ σ'
           
  sym≈ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ ρ' : Sub Δ Γ}
         → ρ ≈ ρ'
         → ρ' ≈ ρ
  
  trans≈ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ ρ' ρ'' : Sub Δ Γ}
           → ρ ≈ ρ'
           → ρ' ≈ ρ''
           → ρ ≈ ρ''

refl~ : ∀ {n α} {Γ : Ctx n} {t : Tm Γ α} → t ~ t
refl~ {t = t} = trans~ (sym~ (subId t)) (subId t)

refl≈ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {ρ : Sub Δ Γ} → ρ ≈ ρ
refl≈ {ρ = ρ} = trans≈ (sym≈ (idL ρ)) (idL ρ)
