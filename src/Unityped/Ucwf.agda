---------------------------------------------------------------------------
-- The notions of unityped categories with families. Record descriptions
-- of object, morphism, and isomorphism in two categories, namely, the
-- categories of ucwfs and λβη-ucwfs. The latter is contains the former
-- and adds some extra structure.
---------------------------------------------------------------------------
module Ucwf where

open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Relation.Binary using (IsEquivalence ; Setoid)

-- An object in the category of Ucwfs

record Ucwf : Set₁ where
  infix 4 _~_
  infix 4 _≈_
  infix 8 _∘_
  
  field
    Tm  : Nat → Set
    Sub : Nat → Nat → Set 
    
    _~_ : ∀ {n} (_ _ : Tm n) → Set
    _≈_ : ∀ {m n} (_ _ : Sub m n) → Set

    IsEquivT : ∀ {n} → IsEquivalence (_~_ {n})
    IsEquivS : ∀ {m n} → IsEquivalence (_≈_ {m} {n})

    id     : ∀ {n} → Sub n n
    _∘_    : ∀ {m n k} → Sub n k → Sub m n → Sub m k
    _[_]   : ∀ {m n} → Tm n → Sub m n → Tm m
    <>     : ∀ {m} → Sub m zero
    <_,_>  : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)
    p      : ∀ {n} → Sub (suc n) n
    q      : ∀ {n} → Tm (suc n)

    id-zero : id {0} ≈ <>

    left-zero : ∀ {m n} {σ : Sub m n} → <> ∘ σ ≈ <>

    idExt : ∀ {n} → id {suc n} ≈ < p , q >
             
    idL : ∀ {m n} {σ : Sub m n} → id ∘ σ ≈ σ
             
    idR : ∀ {m n} {σ : Sub m n} → σ ∘ id ≈ σ
             
    assoc : ∀ {m n κ ι} {σ₁ : Sub n κ} {σ₂ : Sub m n} {σ₃ : Sub ι m}
            → (σ₁ ∘ σ₂) ∘ σ₃ ≈ σ₁ ∘ (σ₂ ∘ σ₃)
 
    subId : ∀ {n} {t : Tm n} → t [ id ] ~ t

    pCons : ∀ {n κ} {σ : Sub n κ} {t} → p ∘ < σ , t > ≈ σ

    qCons : ∀ {m n} {σ : Sub n m} {t} → q [ < σ , t > ] ~ t

    subComp : ∀ {m n k} {t} {σ : Sub m n} {ρ : Sub k m}
              → t [ σ ∘ ρ ] ~ t [ σ ] [ ρ ]

    compExt : ∀ {m n} {σ : Sub n m} {ρ : Sub m n} {t}
              → < σ , t > ∘ ρ ≈ < σ ∘ ρ , t [ ρ ] >
             
    cong-<,> : ∀ {m n} {σ₁ σ₂ : Sub m n} {t₁ t₂}
               → t₁ ~ t₂
               → σ₁ ≈ σ₂
               → < σ₁ , t₁ > ≈ < σ₂ , t₂ >
                
    cong-sub : ∀ {m n} {σ₁ σ₂ : Sub m n} {t₁ t₂}
               → t₁ ~ t₂
               → σ₁ ≈ σ₂
               → t₁ [ σ₁ ] ~ t₂ [ σ₂ ]
                
    cong-∘ : ∀ {m n k} {σ₁ σ₂ : Sub n k} {ρ₁ ρ₂ : Sub m n}
             → σ₁ ≈ σ₂
             → ρ₁ ≈ ρ₂
             → σ₁ ∘ ρ₁ ≈ σ₂ ∘ ρ₂

  setoidTm : ∀ {n} → Setoid _ _
  setoidTm {n} = record { isEquivalence = IsEquivT {n} }

  setoidSub : ∀ {m n} → Setoid _ _
  setoidSub {m} {n} = record { isEquivalence = IsEquivS {m} {n} }

  ⇑ : ∀ {m n} (σ : Sub m n) → Sub (suc m) (suc n)
  ⇑ σ = < σ ∘ p , q >

  weaken : ∀ {m} → Tm m → Tm (suc m)
  weaken = _[ p ]

-- Morphism in the category of Ucwfs

record Ucwf-⇒  (src trg : Ucwf) : Set₁ where
  open Ucwf src 
    renaming (Tm to Tm₁ ; Sub to Sub₁ ; <> to <>₁ ; <_,_> to <_,_>₁ ; _∘_ to _∘₁_
             ; _[_] to _[_]₁ ; q to q₁ ; p to p₁ ; id to id₁ ; _~_ to _~₁_ ; _≈_ to _≈₁_)
  open Ucwf trg 
    renaming (Tm to Tm₂ ; Sub to Sub₂ ; <> to <>₂ ; <_,_> to <_,_>₂ ;_∘_ to _∘₂_
             ; _[_] to _[_]₂ ; q to q₂ ; p to p₂ ; id to id₂ ; _~_ to _~₂_ ; _≈_ to _≈₂_) 
  field
      
    ⟦_⟧  : ∀ {n} → Tm₁ n → Tm₂ n
    ⟦_⟧' : ∀ {m n} → Sub₁ m n → Sub₂ m n
    
    id-preserved : ∀ {n} → ⟦ id₁ {n} ⟧' ≈₂ id₂
    
    q-preserved : ∀ {n} → ⟦ q₁ {n}  ⟧ ~₂ q₂
    
    p-preserved : ∀ {n} → ⟦ p₁ {n}  ⟧' ≈₂ p₂
    
    ∘-preserved : ∀ {m n k} (σ₁ : Sub₁ k n) (σ₂ : Sub₁ m k)
                  → ⟦ σ₁ ∘₁ σ₂ ⟧' ≈₂ ⟦ σ₁ ⟧' ∘₂ ⟦ σ₂ ⟧'

    <>-preserved : ∀ {m} → ⟦ <>₁ {m} ⟧' ≈₂ <>₂

    <,>-preserved : ∀ {m n} (t : Tm₁ m) (σ : Sub₁ m n)
                    → ⟦ < σ , t >₁ ⟧' ≈₂ < ⟦ σ ⟧' , ⟦ t ⟧ >₂

    sub-preserved : ∀ {m n} (t : Tm₁ n) (σ : Sub₁ m n)
                    → ⟦ t [ σ ]₁ ⟧ ~₂ ⟦ t ⟧ [ ⟦ σ ⟧' ]₂

-- Isomorphism in the category of ucwfs

record Ucwf-≅ {u₁ u₂} (u₁⇒ : Ucwf-⇒ u₁ u₂) (u₂⇒ : Ucwf-⇒ u₂ u₁) : Set₁ where
  open Ucwf u₁
    renaming (Tm to Tm₁ ; Sub to Sub₁ ; <> to <>₁ ; <_,_> to <_,_>₁ ; _∘_ to _∘₁_
             ; _[_] to _[_]₁ ; q to q₁ ; p to p₁ ; id to id₁ ; _~_ to _~₁_ ; _≈_ to _≈₁_)
  open Ucwf u₂
    renaming (Tm to Tm₂ ; Sub to Sub₂ ; <> to <>₂ ; <_,_> to <_,_>₂ ;_∘_ to _∘₂_
             ; _[_] to _[_]₂ ; q to q₂ ; p to p₂ ; id to id₂ ; _~_ to _~₂_ ; _≈_ to _≈₂_) 
  open Ucwf-⇒ u₁⇒ renaming (⟦_⟧ to ⟦_⟧₁ ; ⟦_⟧' to ⟦_⟧'₁)
  open Ucwf-⇒ u₂⇒ renaming (⟦_⟧ to ⟦_⟧₂ ; ⟦_⟧' to ⟦_⟧'₂)
  field
    left-inv-tm   : ∀ {n} (t : Tm₁ n) → ⟦ ⟦ t ⟧₁ ⟧₂ ~₁ t
    right-inv-tm  : ∀ {n} (t : Tm₂ n) → ⟦ ⟦ t ⟧₂ ⟧₁ ~₂ t  
    left-inv-sub  : ∀ {m n} (ρ : Sub₁ m n) → ⟦ ⟦ ρ ⟧'₁ ⟧'₂ ≈₁ ρ
    right-inv-sub : ∀ {m n} (ρ : Sub₂ m n) → ⟦ ⟦ ρ ⟧'₂ ⟧'₁ ≈₂ ρ

-- Object in the category of λβη-ucwfs

record λβη-ucwf : Set₁ where
  field
    ucwf : Ucwf
  open Ucwf ucwf
  field
    lam : ∀ {n} → Tm (suc n) → Tm n
    app : ∀ {n} → Tm n → Tm n → Tm n
    
    subApp : ∀ {n m} {σ : Sub m n} {t u}
             → (app t u) [ σ ] ~ app (t [ σ ]) (u [ σ ])
    
    subLam : ∀ {n m} {σ : Sub m n} {t}
             → lam t [ σ ] ~ lam (t [ ⇑ σ ])

    β : ∀ {n} {t : Tm (suc n)} {u} → app (lam t) u ~ t [ < id , u > ]        

    η : ∀ {n} {t : Tm n} → lam (app  (t [ p ]) q) ~ t

    cong-lam : ∀ {n} {t₁ t₂ : Tm (suc n)}
               → t₁ ~ t₂
               → lam t₁ ~ lam t₂
              
    cong-app : ∀ {n} {t₁ u₁ t₂ u₂ : Tm n}
               → t₁ ~ t₂
               → u₁ ~ u₂
               → app t₁ u₁ ~ app t₂ u₂

-- Morphism in the category of λβη-ucwfs

record λβη-ucwf-⇒ (src trg : λβη-ucwf) : Set₁ where
  open λβη-ucwf src renaming (ucwf to ucwf₁ ; lam to lam₁ ; app to app₁)
  open λβη-ucwf trg renaming (ucwf to ucwf₂ ; lam to lam₂ ; app to app₂)
  open Ucwf ucwf₁ renaming (Tm to Tm₁ ; _~_ to _~₁_)
  open Ucwf ucwf₂ renaming (Tm to Tm₂ ; _~_ to _~₂_)
  field
    ucwf-⇒ : Ucwf-⇒ ucwf₁ ucwf₂
  open Ucwf-⇒ ucwf-⇒
  field
    lam-preserved : ∀ {n} {t : Tm₁ (suc n)} → ⟦ lam₁ t ⟧ ~₂ lam₂ ⟦ t ⟧
    app-preserved : ∀ {n} {f t : Tm₁ n} → ⟦ app₁ f t ⟧ ~₂ app₂ ⟦ f ⟧ ⟦ t ⟧

-- Isomorphism in the category of λβη-ucwfs

record λβη-ucwf-≅ {λu₁ λu₂} (λu₁-⇒ : λβη-ucwf-⇒ λu₁ λu₂)
                            (λu₂-⇒ : λβη-ucwf-⇒ λu₂ λu₁) : Set₁ where
  open λβη-ucwf-⇒ λu₁-⇒ renaming (ucwf-⇒ to u-⇒₁)
  open λβη-ucwf-⇒ λu₂-⇒ renaming (ucwf-⇒ to u-⇒₂)
  open λβη-ucwf λu₁ renaming (ucwf to u₁)
  open λβη-ucwf λu₂ renaming (ucwf to u₂)
  open Ucwf-⇒ u-⇒₁ renaming (⟦_⟧ to ⟦_⟧₁ ; ⟦_⟧' to ⟦_⟧'₁)
  open Ucwf-⇒ u-⇒₂ renaming (⟦_⟧ to ⟦_⟧₂ ; ⟦_⟧' to ⟦_⟧'₂)
  open Ucwf u₁
    renaming (Tm to Tm₁ ; Sub to Sub₁ ; <> to <>₁ ; <_,_> to <_,_>₁ ; _∘_ to _∘₁_
             ; _[_] to _[_]₁ ; q to q₁ ; p to p₁ ; id to id₁ ; _~_ to _~₁_ ; _≈_ to _≈₁_)
  open Ucwf u₂
    renaming (Tm to Tm₂ ; Sub to Sub₂ ; <> to <>₂ ; <_,_> to <_,_>₂ ;_∘_ to _∘₂_
             ; _[_] to _[_]₂ ; q to q₂ ; p to p₂ ; id to id₂ ; _~_ to _~₂_ ; _≈_ to _≈₂_)   
  field
    left-inv-tm   : ∀ {n} (t : Tm₁ n) → ⟦ ⟦ t ⟧₁ ⟧₂ ~₁ t
    right-inv-tm  : ∀ {n} (t : Tm₂ n) → ⟦ ⟦ t ⟧₂ ⟧₁ ~₂ t
    
    left-inv-sub  : ∀ {m n} (σ : Sub₁ m n) → ⟦ ⟦ σ ⟧'₁ ⟧'₂ ≈₁ σ
    right-inv-sub : ∀ {m n} (σ : Sub₂ m n) → ⟦ ⟦ σ ⟧'₂ ⟧'₁ ≈₂ σ
