module Ucwf where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)

--postulate Hom : Nat → Nat → Set

record Ucwf (Term : Nat → Set) : Set₁ where
  private
    Hom : Nat → Nat → Set
    Hom m n = Vec (Term m) n
  field
    id    : (n : Nat) {m : Nat} → Hom m n
    comp  : (m n k : Nat) → Hom n k → Hom m n → Hom m k
    subs  : (m n : Nat) → Term n → Hom m n → Term m
    ⟨_,_⟩ : (m n : Nat) → Hom m n → Term m → Hom m (suc n)
    ⟨⟩    : (m : Nat) → Hom m 0
    p     : (n : Nat) → Hom (suc n) n
    q     : (n : Nat) → Term (suc n)
    
    ∘ε     : ∀ {m n : Nat} (ts : Hom m n) → comp m n zero (⟨⟩ n) ts ≡ ⟨⟩ m
    ∘lid   : ∀ {m n : Nat} (ts : Hom m n) → (comp m n n (id n) ts) ≡ ts
    ∘rid   : ∀ {m n : Nat} (ts : Hom m n) → (comp m m n ts (id m)) ≡ ts
    ∘assoc : ∀ {m n k : Nat} (ts : Hom n k) (us : Hom m n) (vs : Hom m m) →
             comp m m k (comp m n k ts us) vs ≡ comp m n k ts (comp m m n us vs)
    subid  : ∀ {m n : Nat} (t : Term n) → subs n n t (id n) ≡ t

record λβ-ucwf (Term : Nat → Set) : Set₁ where
  open Ucwf public
  field
    uc  : Ucwf Term
    lam : (n : Nat) → Term (suc n) → Term n
    app : (n : Nat) → Term n → Term n → Term n
    β   : {n m : Nat} → {t : Term (suc n)} → {u : Term n} → app n (lam n t) u ≡ subs uc n m {!t!} {!!}
