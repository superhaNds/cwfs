-----------------------------------------------------------------------------
-- The notion of a ucwf and its extensions with extra structure
-- Ucwf morphisms between ucwfs after
-- They represent objects and morphisms in the respective category
-- of ucwfs with the appropriate structure
-----------------------------------------------------------------------------
module Unityped.Ucwf where

open import Level renaming (zero to lzero ; suc to  lsuc)
open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Relation.Binary using (Rel ; IsEquivalence ; Setoid)

-----------------------------------------------------------------------------
-- The sorts, operator symbols, and axioms of a ucwf

record Ucwf : Set₁ where
  infix 4 _≈_
  infix 4 _≋_
  infix 8 _∘_
  
  field
    -- Contexts are natural numbers
   
    -- Terms and substitutions (sorts)
    
    Tm   : Nat → Set
    Sub  : Nat → Nat → Set 

    -- Relations for equality of terms and substitutions
    
    _≈_   : ∀ {n} → (t₁ t₂ : Tm n) → Set
    _≋_   : ∀ {m n} → (σ₁ σ₂ : Sub m n) → Set

    IsEquivT : ∀ {n} → IsEquivalence (_≈_ {n})
    IsEquivS : ∀ {m n} → IsEquivalence (_≋_ {m} {n})

    -- operators
    
    id     : ∀ {n} → Sub n n
    _∘_    : ∀ {m n k} → Sub n k → Sub m n → Sub m k
    _[_]   : ∀ {m n} → Tm n → Sub m n → Tm m
    <>     : ∀ {m} → Sub m zero
    <_,_>  : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)
    p      : ∀ {n} → Sub (suc n) n
    q      : ∀ {n} → Tm (suc n)
    
    -- cwf axioms

    -- zero length id is the empty substitution
    
    id₀ : id {0} ≋ <>

    -- <> is a a left zero for composition
  
    left-zero : ∀ {m n} (σ : Sub m n) → <> ∘ σ ≋ <>

    -- extended identity is the projection morphism with the last variable

    idExt : ∀ {n} → id {suc n} ≋ < p , q >

    -- category of substitutions
             
    idL : ∀ {m n} (σ : Sub m n) → id ∘ σ ≋ σ
             
    idR : ∀ {m n} (σ : Sub m n) → σ ∘ id ≋ σ
             
    assoc : ∀ {m n κ ι} (σ₁ : Sub n κ) (σ₂ : Sub m n) (σ₃ : Sub ι m)
            → (σ₁ ∘ σ₂) ∘ σ₃ ≋ σ₁ ∘ (σ₂ ∘ σ₃)

    -- Substituting in id doesn't affect terms
 
    subId : ∀ {n} (t : Tm n) → t [ id ] ≈ t

    -- p is the first projection

    pCons : ∀ {n κ} (σ : Sub n κ) t → p ∘ < σ , t > ≋ σ

    -- q is the second projection

    qCons : ∀ {m n} (σ : Sub n m) t → q [ < σ , t > ] ≈ t

    -- Substituting under a composition

    subComp : ∀ {m n κ} (σ : Sub m n) (ρ : Sub κ m) t
              → t [ σ ∘ ρ ] ≈ t [ σ ] [ ρ ]

    -- Composing with an extended substitution

    compExt : ∀ {m n} (σ : Sub n m) (ρ : Sub m n) t
              → < σ , t > ∘ ρ ≋ < σ ∘ ρ , t [ ρ ] >
             
    -- congruence rules for operators
    
    cong-<,> : ∀ {m n} {σ ρ : Sub m n} {t u}
               → t ≈ u
               → σ ≋ ρ
               → < σ , t > ≋ < ρ , u >
                
    cong-sub : ∀ {m n} {σ ρ : Sub m n} {t u}
               → t ≈ u
               → σ ≋ ρ
               → t [ σ ] ≈ u [ ρ ]
                
    cong-∘ : ∀ {m n k} {σ₁ σ₂ : Sub n k} {ρ₁ ρ₂ : Sub m n}
             → σ₁ ≋ σ₂
             → ρ₁ ≋ ρ₂
             → σ₁ ∘ ρ₁ ≋ σ₂ ∘ ρ₂

  setoidT : ∀ {n} → Setoid _ _
  setoidT {n} = record { isEquivalence = IsEquivT {n} }

  setoidS : ∀ {m n} → Setoid _ _
  setoidS {m} {n} = record { isEquivalence = IsEquivS {m} {n} }

  ⇑ : ∀ {m n} (σ : Sub m n) → Sub (suc m) (suc n)
  ⇑ σ = < σ ∘ p , q >

  weaken : ∀ {m} → Tm m → Tm (suc m)
  weaken = _[ p ]

-- Extending the pure ucwf with lambdas and applications

record Lambda-ucwf : Set₁ where
  field
    ucwf : Ucwf
    
  open Ucwf ucwf public
  
  field

    -- λ abstraction and application

    lam : ∀ {n} → Tm (suc n) → Tm n
    app : ∀ {n} → Tm n → Tm n → Tm n

    -- substituting under app and lam
    
    subApp : ∀ {n m} (σ : Sub m n) t u
             → app (t [ σ ]) (u [ σ ]) ≈ (app t u) [ σ ]
    
    subLam : ∀ {n m} (σ : Sub m n) t
             → lam t [ σ ] ≈ lam (t [ ⇑ σ ])
    
    cong-lam : ∀ {n} {t₁ t₂ : Tm (suc n)}
               → t₁ ≈ t₂
               → lam t₁ ≈ lam t₂
              
    cong-app : ∀ {n} {t₁ u₁ t₂ u₂ : Tm n}
               → t₁ ≈ t₂
               → u₁ ≈ u₂
               → app t₁ u₁ ≈ app t₂ u₂

-- Extending a ucwf with lambdas up to β and η

record Lambda-βη-ucwf : Set₁ where
  field
    lambda-ucwf : Lambda-ucwf 
  open Lambda-ucwf lambda-ucwf public

  field

   -- beta and eta equalities

    β : ∀ {n} {t : Tm (suc n)} {u} → app (lam t) u ≈ t [ < id , u > ]        
    η : ∀ {n} {t : Tm n} → lam (app (weaken t) q) ≈ t

----------------------------------------------------------------------------------------------------
-- Ucwf morphisms

-- Pure Ucwf morphism

record Ucwf-Morphism  (src trg : Ucwf) : Set₁ where
  open Ucwf src
    renaming (Tm to Tm₁ ; Sub to Sub₁ ; <> to <>₁ ; <_,_> to <_,_>₁ ; _∘_ to _∘₁_
             ; _[_] to _[_]₁ ; q to q₁ ; p to p₁ ; id to id₁ ; _≈_ to _≈₁_ ; _≋_ to _≋₁_)
  open Ucwf trg
    renaming (Tm to Tm₂ ; Sub to Sub₂ ; <> to <>₂ ; <_,_> to <_,_>₂ ;_∘_ to _∘₂_
             ; _[_] to _[_]₂ ; q to q₂ ; p to p₂ ; id to id₂ ; _≈_ to _≈₂_ ; _≋_ to _≋₂_) 
  field
  
    -- maps from terms and substitutions
    
    ⟦_⟧   : ∀ {n} → Tm₁ n → Tm₂ n
    ⟦_⟧'  : ∀ {m n} → Sub₁ m n → Sub₂ m n

    -- Ucwf structure is preserved
    
    id-preserved : ∀ {n} → ⟦ id₁ {n} ⟧' ≋₂ id₂
    
    q-preserved : ∀ {n} → ⟦ q₁ {n}  ⟧ ≈₂ q₂
    
    p-preserved : ∀ {n} → ⟦ p₁ {n}  ⟧' ≋₂ p₂
    
    ∘-preserved : ∀ {m n k} (σ₁ : Sub₁ k n) (σ₂ : Sub₁ m k)
                  → ⟦ σ₁ ∘₁ σ₂ ⟧' ≋₂ ⟦ σ₁ ⟧' ∘₂ ⟦ σ₂ ⟧'

    <>-preserved : ∀ {m} → ⟦ <>₁ {m} ⟧' ≋₂ <>₂

    <,>-preserved : ∀ {m n} (t : Tm₁ m) (σ : Sub₁ m n)
                    → ⟦ < σ , t >₁ ⟧' ≋₂ < ⟦ σ ⟧' , ⟦ t ⟧ >₂

    sub-preserved : ∀ {m n} (t : Tm₁ n) (σ : Sub₁ m n)
                    → ⟦ t [ σ ]₁ ⟧ ≈₂ ⟦ t ⟧ [ ⟦ σ ⟧' ]₂

-- λ-ucwf morphism

record Lambda-Ucwf-Morphism (src trg : Lambda-ucwf) : Set₁ where
  open Lambda-ucwf src renaming (ucwf to ucwf₁ ; Tm to Tm₁ ; lam to lam₁ ; app to app₁)
  open Lambda-ucwf trg renaming (ucwf to ucwf₂ ; Tm to Tm₂ ; lam to lam₂ ; app to app₂ ; _≈_ to _≈₂_)

  -- A pure ucwf morphism
  
  field
    ucwf-arr : Ucwf-Morphism ucwf₁ ucwf₂
  open Ucwf-Morphism ucwf-arr

  -- lambda and application structures are preserved
  
  field
    lam-preserved : ∀ {n} {t : Tm₁ (suc n)} → ⟦ lam₁ t ⟧ ≈₂ lam₂ ⟦ t ⟧
    app-preserved : ∀ {n} {f t : Tm₁ n} → ⟦ app₁ f t ⟧ ≈₂ app₂ ⟦ f ⟧ ⟦ t ⟧

