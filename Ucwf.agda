module Ucwf where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Ucwf (Term : Nat → Set) : Set₁ where
  private
    Hom : Nat → Nat → Set
    Hom m n = Vec (Term m) n
  field
    id    : (n : Nat) → Hom n n
    comp  : (m n k : Nat) → Hom n k → Hom m n → Hom m k
    subs  : (m n : Nat) → Term n → Hom m n → Term m
    _,_<_,_> : (m n : Nat) → Hom m n → Term m → Hom m (suc n)
    <>    : (m : Nat) → Hom m 0
    p     : (n : Nat) → Hom (suc n) n
    q     : (n : Nat) → Term (suc n)

    ∘ε     : ∀ {m n : Nat} (ts : Hom m n) → comp m n zero (<> n) ts ≡ <> m
    id0    : id zero ≡ <> zero
    id<p,q> : ∀ {n : Nat} → id (suc n) ≡ suc n , n < p n , q n >
    ∘lid   : ∀ {m n : Nat} (ts : Hom m n) → (comp m n n (id n) ts) ≡ ts
    ∘rid   : ∀ {m n : Nat} (ts : Hom m n) → (comp m m n ts (id m)) ≡ ts
    ∘assoc : ∀ {m n k : Nat} (ts : Hom n k) (us : Hom m n) (vs : Hom m m) →
             comp m m k (comp m n k ts us) vs ≡ comp m n k ts (comp m m n us vs)
    subid  : ∀ {m n : Nat} (t : Term n) → subs n n t (id n) ≡ t
    p∘<γ∘α>  : ∀ {m n k : Nat} → {t : Term n} → {ts : Hom n k} → comp n (suc k) k (p k) (n , k < ts , t >) ≡ ts
    q[<γ,α>] : ∀ {m n : Nat} {ts t} → subs n (suc m) (q m) (n , m < ts , t >) ≡ t
    sub∘ : ∀ {m n k : Nat} → ∀ {t ts us} → subs m n t (comp m n n ts us) ≡ subs m n (subs n n t ts) us

record λβ-ucwf (Term : Nat → Set) : Set₁ where
  field
    ucwf : Ucwf Term
  open Ucwf ucwf public
  field
    lam : (n : Nat) → Term (suc n) → Term n
    app : (n : Nat) → Term n → Term n → Term n
    β   : {n m : Nat} {t : Term (suc n)} {u : Term n} → app n (lam n t) u ≡ subs n (suc n) t (n , n < id n , u >)
    η   : {n : Nat} {t : Term (suc n)} → lam n (app (suc n) t (q n)) ≡ {!!}
