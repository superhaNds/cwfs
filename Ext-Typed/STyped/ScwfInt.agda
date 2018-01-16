-------------------------------------------------------------------------
-- Simply typed category with families as a generalized algebraic
-- theory using directly typed terms. Terms are intrinsically typed
-- so there is no typing relation on-top.
-------------------------------------------------------------------------
module Ext-Typed.STyped.ScwfInt where

open import Data.Nat renaming (ℕ to Nat)
open import Ext-Typed.STyped.CtxType

-------------------------------------------------------------------------
-- Terms and Substitutions as mutually recursive data types

data Tm : ∀ {n} (Γ : Ctx n) (α : Ty) → Set
data Subst : ∀ {n m} → Ctx m → Ctx n → Set

data Tm where

  q    : ∀ {n α} {Γ : Ctx n} → Tm (Γ , α) α
  
  _[_] : ∀ {m n} {Γ : Ctx n}
           {Δ : Ctx m} {α} → Tm Γ α
                           → Subst Γ Δ
                           → Tm Δ α
  
  app  : ∀ {n α β} {Γ : Ctx n} → Tm Γ (α ⇨ β)
                               → Tm Γ α
                               → Tm Γ β
  
  lam  : ∀ {n α β} {Γ : Ctx n} → Tm (Γ , α) β
                               → Tm Γ (α ⇨ β)
         
data Subst where

  <>     : ∀ {n} {Γ : Ctx n} → Subst ε Γ
  
  id     : ∀ {n} {Γ : Ctx n} → Subst Γ Γ
  
  p      : ∀ {n α} {Γ : Ctx n} → Subst Γ (Γ , α)
  
  _∘_    : ∀ {m n k} {Γ : Ctx n}
             {Δ : Ctx m} {Θ : Ctx k} → Subst Θ Γ
                                     → Subst Γ Δ
                                     → Subst Θ Δ
                                     
  <_,_>  : ∀ {m n} {Γ : Ctx n}
             {Δ : Ctx m} {α} → Subst Δ Γ
                             → Tm Γ α
                             → Subst (Δ , α) Γ

infix 6 _~_
infix 6 _~~_

-- Equality of terms and substitutions as inductive equivalence relations with
-- introduction rules for all cwf axioms

data _~_  : ∀ {n α} {Γ : Ctx n} (t₁ t₂ : Tm Γ α) → Set
data _~~_ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (γ₁ γ₂ : Subst Γ Δ) → Set

data _~_ where

  tmId : ∀ {n α} {Γ : Ctx n} (t : Tm Γ α) →
          t [ id ] ~ t
          
  q[]  : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m} (t : Tm Γ α) (ρ : Subst Δ Γ) →
          q [ < ρ , t > ] ~ t
         
  clos : ∀ {m n k α} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
           (t : Tm Δ α) (ρ : Subst Δ Γ) (σ : Subst Γ Θ) →
          t [ ρ ∘ σ ] ~ t [ ρ ] [ σ ]

  appCm : ∀ {m n α β} {Γ : Ctx n} {Δ : Ctx m}
            (t : Tm Γ (α ⇨ β)) (u : Tm Γ α) (ρ : Subst Γ Δ) →
           app (t [ ρ ]) (u [ ρ ]) ~ app t u [ ρ ]

  lamCm : ∀ {m n α β} {Γ : Ctx n} {Δ : Ctx m}
            (t : Tm (Γ , α) β) (ρ  : Subst Γ Δ) →
           lam t [ ρ ] ~ lam (t [ < ρ ∘ p , q > ])
         
  cong-[] : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m}
              {t t' : Tm Γ α} {ρ ρ' : Subst Γ Δ} →
             t ~ t' →
             ρ ~~ ρ' →
             t [ ρ ] ~ t' [ ρ' ]
            
  cong-app : ∀ {n α β} {Γ : Ctx n}
               {t u : Tm Γ (α ⇨ β)} {t' u' : Tm Γ α} →
              t ~ u →
              t' ~ u' →
              app t t' ~ app u u'
             
  cong-lam : ∀ {n α β} {Γ : Ctx n} {t t' : Tm (Γ , α) β} →
              t ~ t' →
              lam t ~ lam t'
             
  sym~ : ∀ {n α} {Γ : Ctx n} {t t' : Tm Γ α} →
          t ~ t' →
          t' ~ t
         
  trans~ : ∀ {n α} {Γ : Ctx n} {t t' t'' : Tm Γ α} →
            t ~ t' →
            t' ~ t'' →
            t ~ t''
  
data _~~_ where

  id₀  : id {Γ = ε} ~~ <>
  
  <>∘  : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (ρ : Subst Γ Δ) →
          <> ∘ ρ ~~ <>
  
  varp : ∀ {n α} {Γ : Ctx n} →
          id {Γ = Γ , α} ~~ < p , q >
  
  idL  : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Subst Γ Δ) →
          id ∘ ρ ~~ ρ
  
  idR  : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Subst Δ Γ) →
          ρ ∘ id ~~ ρ
  
  asso : ∀ {m n k l} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {Λ : Ctx l} →
           (ρ : Subst Θ Δ) (σ : Subst Δ Γ) (τ : Subst Γ Λ) →
          (ρ ∘ σ) ∘ τ ~~ ρ ∘ (σ ∘ τ)
         
  pCons : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m} (t : Tm Δ α) (ρ : Subst Γ Δ) →
          p ∘ < ρ , t > ~~ ρ
          
  maps : ∀ {m n k α} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
           (t : Tm Δ α) (ρ : Subst Θ Δ) (σ : Subst Δ Γ) →
          < ρ , t > ∘ σ ~~ < ρ ∘ σ , t [ σ ] >
         
  cong-<,> : ∀ {m n α} {Γ : Ctx n} {Δ : Ctx m} {t t' : Tm Γ α} {ρ ρ' : Subst Δ Γ} →
              t ~ t' →
              ρ ~~ ρ' →
              < ρ , t > ~~ < ρ' , t' >
            
  cong-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
             {ρ σ : Subst Θ Δ} {ρ' σ' : Subst Δ Γ} →
            ρ ~~ σ →
            ρ' ~~ σ' →
            ρ ∘ ρ' ~~ σ ∘ σ'
           
  sym~~ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ ρ' : Subst Δ Γ} →
           ρ ~~ ρ' →
           ρ' ~~ ρ
  
  trans~~ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ ρ' ρ'' : Subst Δ Γ} →
             ρ ~~ ρ' →
             ρ' ~~ ρ'' →
             ρ ~~ ρ''

refl~ : ∀ {n α} {Γ : Ctx n} {t : Tm Γ α} → t ~ t
refl~ {t = t} = trans~ (sym~ (tmId t)) (tmId t)

refl~~ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {ρ : Subst Δ Γ} → ρ ~~ ρ
refl~~ {ρ = ρ} = trans~~ (sym~~ (idL ρ)) (idL ρ)
