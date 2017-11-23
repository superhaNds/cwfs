-----------------------------------------------------------------------------
-- The notion of a ucwf and its extensions with lambdas and others
-----------------------------------------------------------------------------
module Unityped.Ucwf where

open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary

-----------------------------------------------------------------------------
-- The sorts, operator symbols, and axioms of a ucwf gathered as a record

record Ucwf : Set₁ where
  infix 4 _~_
  infix 4 _~~_
  infix 9 _∘_
  
  field
    -- the types for terms and substitutions 
    Term   : Nat → Set
    Hom    : Nat → Nat → Set

    -- two relations regarding equality of terms and substitutions
    _~_   : ∀ {n} → Rel (Term n) lzero
    _~~_   : ∀ {m n} → Rel (Hom m n) lzero

    -- operator symbols
    id     : {n : Nat} → Hom n n
    <>     : {m : Nat} → Hom m 0
    p      : {n : Nat} → Hom (suc n) n
    q      : {n : Nat} → Term (suc n)
    _∘_    : {m n k : Nat} → Hom n k → Hom m n → Hom m k
    _[_]   : {m n : Nat} → Term n → Hom m n → Term m
    <_,_>  : {m n : Nat} → Hom m n → Term m → Hom m (suc n)

    -- axioms
    id₀   : id {0} ~~ <>
    ∘<>   : ∀ {m n : Nat} (ts : Hom m n) → <> ∘ ts ~~ <> 
    varp  : ∀ {n : Nat} → id {suc n} ~~ < p , q >
    idL   : ∀ {m n : Nat} (ts : Hom m n) → id ∘ ts ~~ ts
    idR   : ∀ {m n : Nat} (ts : Hom m n) → ts ∘ id ~~ ts
    assoc : ∀ {m n κ ι : Nat} (ts : Hom n κ) (us : Hom m n) (vs : Hom ι m) →
             (ts ∘ us) ∘ vs ~~ ts ∘ (us ∘ vs)
    terId : ∀ {m n : Nat} (t : Term n) → t [ id ] ~ t
    pCons : ∀ {m n κ : Nat} → (t : Term n) → (ts : Hom n κ) → p ∘ < ts , t > ~~ ts
    qCons : ∀ {m n : Nat} (t : Term n) (ts : Hom n m) → q [ < ts , t > ] ~ t
    clos  : ∀ {m n κ : Nat} (t : Term n) (ts : Hom m n) (us : Hom κ m) →
             t [ ts ∘  us ] ~ t [ ts ] [ us ]
    maps  : ∀ {m n : Nat} (t : Term n) (ts : Hom n m) (us : Hom m n) →
             < ts , t > ∘ us ~~ < ts ∘ us , t [ us ] >
             
    -- congruence rules for operators
    cong-<,> : ∀ {m n} {t u : Term m} {ts us : Hom m n} →
                t ~ u → ts ~~ us → < ts , t > ~~ < us , u >
    cong-[_] : ∀ {m n} {t u : Term n} {ts us : Hom m n} →
                t ~ u → ts ~~ us → t [ ts ] ~ u [ us ]
    cong-∘   : ∀ {m n k} {ts vs : Hom n k} {us zs : Hom m n} →
                ts ~~ vs → us ~~ zs → ts ∘ us ~~ vs ∘ zs
  
  ⇑ : ∀ {m n} (ts : Hom m n) → Hom (suc m) (suc n)
  ⇑ ts = < ts ∘ p , q >

  weaken : ∀ {m} → Term m → Term (suc m)
  weaken {m} = _[ p ] 

-- Extending the pure ucwf with lambdas and applications

record Lambda-ucwf : Set₁ where
  infix 10 _·_ 
  field
    ucwf : Ucwf   
  open Ucwf ucwf public  
  field
    ƛ   : {n : Nat} → Term (suc n) → Term n
    _·_ : {n : Nat} → Term n → Term n → Term n
    cong-ƛ : ∀ {n} {t u : Term (suc n)} → t ~ u → ƛ t ~ ƛ u
    cong-· : ∀ {n} {t u t′ u′ : Term n} → t ~ t′ → u ~ u′ → t · u ~ t′ · u′
    app : {n m : Nat} (t u : Term n) (ts : Hom m n) → (t [ ts ]) · (u [ ts ]) ~ (t · u) [ ts ]
    abs : {n m : Nat} (t : Term (suc n)) (ts : Hom m n) → ƛ t [ ts ] ~ ƛ (t [ ⇑ ts ])

-- Extending the ucwf with lambdas up to β and η

record Lambda-βη-ucwf : Set₁ where
  field
    lambda-ucwf : Lambda-ucwf

  open Lambda-ucwf lambda-ucwf public

  field
    β   : {n : Nat} (t : Term (suc n)) (u : Term n) → ƛ t · u ~ t [ < id , u > ]
    η   : {n : Nat} (t : Term n) → ƛ (weaken t · q) ~ t
    
