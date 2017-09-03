module Ucwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Ucwf (Term : Nat → Set) : Set₁ where
  private
    Hom : Nat → Nat → Set
    Hom m n = Vec (Term m) n
  field
    id         : (n : Nat) → Hom n n
    <>         : (m : Nat) → Hom m 0
    p          : (n : Nat) → Hom (suc n) n
    q          : (n : Nat) → Term (suc n)
    _,_,_⟨_∘_⟩ : (m n k : Nat) → Hom n k → Hom m n → Hom m k
    _,_▹_[_]   : (m n : Nat) → Term n → Hom m n → Term m
    _,_<_,_>   : (m n : Nat) → Hom m n → Term m → Hom m (suc n)

    id₀      : id zero ≡ <> zero
    ∘<>      : ∀ {m n : Nat} (ts : Hom m n) → (m , n , zero ⟨ <> n ∘ ts ⟩) ≡ <> m
    id<p,q>  : ∀ {n : Nat} → id (suc n) ≡ suc n , n < p n , q n >
    ∘lid     : ∀ {m n : Nat} (ts : Hom m n) → (m , n , n ⟨ (id n) ∘ ts ⟩) ≡ ts
    ∘rid     : ∀ {m n : Nat} (ts : Hom m n) → (m , m , n ⟨ ts ∘ (id m) ⟩) ≡ ts
    ∘asso    : ∀ {m n k p : Nat} (ts : Hom n k) (us : Hom m n) (vs : Hom p m) →
                 p , m , k ⟨ (m , n , k ⟨ ts ∘ us ⟩) ∘ vs ⟩
                 ≡ p , n , k ⟨ ts ∘ (p , m , n ⟨ us ∘ vs ⟩)⟩
    subid    : ∀ {m n : Nat} (t : Term n) → (n , n ▹ t [ id n ]) ≡ t
    p∘<γ∘α>  : ∀ {m n k : Nat} → {t : Term n} → {ts : Hom n k} →
                 n , (suc k) , k ⟨ p k ∘ (n , k < ts , t >)⟩ ≡ ts
    q[<γ,α>] : ∀ {m n : Nat} {ts t} → n , (suc m) ▹ (q m) [ n , m < ts , t > ] ≡ t
    ∘sub     : ∀ {m n : Nat} → ∀ {t ts us} →
                 m , n ▹ t [ m , n , n ⟨ ts ∘  us ⟩ ]
                 ≡ m , n ▹ (n , n ▹ t [ ts ]) [ us ]
    <δ,α>∘γ  : ∀ {m n : Nat} → ∀ {t ts us} →
                 m , n , suc m ⟨ (n , m < ts , t >) ∘ us ⟩
                 ≡ m , m < m , n , m ⟨ ts ∘ us ⟩ , (m , n ▹ t [ us ]) >

record λβ-ucwf (Term : Nat → Set) : Set₁ where
  field
    ucwf : Ucwf Term
  open Ucwf ucwf public
  field
    lam : (n : Nat) → Term (suc n) → Term n
    app : (n : Nat) → Term n → Term n → Term n
    β   : {n : Nat} {t : Term (suc n)} {u : Term n}
            → app n (lam n t) u ≡  n , (suc n) ▹ t [ n , n < id n , u > ]
    η   : {n : Nat} {t : Term (suc n)} → lam n (app (suc n) t (q n)) ≡ {!!} -- needs Term n but t ∈ Term (suc n), weaken it?
