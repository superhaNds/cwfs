module Ucwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Ucwf (Term : Nat → Set) : Set₁ where
  private
    Hom : Nat → Nat → Set
    Hom μ ν = Vec (Term μ) ν
  field
    id         : (ν : Nat) → Hom ν ν
    <>         : (μ : Nat) → Hom μ 0
    p          : (ν : Nat) → Hom (suc ν) ν
    q          : (ν : Nat) → Term (suc ν)
    _,_,_⟨_∘_⟩ : (μ ν k : Nat) → Hom ν k → Hom μ ν → Hom μ k
    _,_▹_[_]   : (μ ν : Nat) → Term ν → Hom μ ν → Term μ
    _,_<_,_>   : (μ ν : Nat) → Hom μ ν → Term μ → Hom μ (suc ν)

    id₀      : id zero ≡ <> zero
    ∘<>      : ∀ {μ ν : Nat} (ts : Hom μ ν) → (μ , ν , zero ⟨ <> ν ∘ ts ⟩) ≡ <> μ
    id<p,q>  : ∀ {ν : Nat} → id (suc ν) ≡ suc ν , ν < p ν , q ν >
    ∘lid     : ∀ {μ ν : Nat} (ts : Hom μ ν) → (μ , ν , ν ⟨ (id ν) ∘ ts ⟩) ≡ ts
    ∘rid     : ∀ {μ ν : Nat} (ts : Hom μ ν) → (μ , μ , ν ⟨ ts ∘ (id μ) ⟩) ≡ ts
    ∘asso    : ∀ {μ ν k p : Nat} (ts : Hom ν k) (us : Hom μ ν) (vs : Hom p μ) →
                 p , μ , k ⟨ (μ , ν , k ⟨ ts ∘ us ⟩) ∘ vs ⟩
                 ≡ p , ν , k ⟨ ts ∘ (p , μ , ν ⟨ us ∘ vs ⟩)⟩
    subid    : ∀ {μ ν : Nat} (t : Term ν) → (ν , ν ▹ t [ id ν ]) ≡ t
    p∘<γ∘α>  : ∀ {μ ν k : Nat} → {t : Term ν} → {ts : Hom ν k} →
                 ν , (suc k) , k ⟨ p k ∘ (ν , k < ts , t >)⟩ ≡ ts
    q[<γ,α>] : ∀ {μ ν : Nat} {ts t} → ν , (suc μ) ▹ (q μ) [ ν , μ < ts , t > ] ≡ t
    ∘sub     : ∀ {μ ν : Nat} → ∀ {t ts us} →
                 μ , ν ▹ t [ μ , ν , ν ⟨ ts ∘  us ⟩ ]
                 ≡ μ , ν ▹ (ν , ν ▹ t [ ts ]) [ us ]
    <δ,α>∘γ  : ∀ {μ ν : Nat} → ∀ {t ts us} →
                 μ , ν , suc μ ⟨ (ν , μ < ts , t >) ∘ us ⟩
                 ≡ μ , μ < μ , ν , μ ⟨ ts ∘ us ⟩ , (μ , ν ▹ t [ us ]) >

record λβ-ucwf (Term : Nat → Set) : Set₁ where
  field
    ucwf : Ucwf Term
  open Ucwf ucwf public
  field
    lam : (ν : Nat) → Term (suc ν) → Term ν
    app : (ν : Nat) → Term ν → Term ν → Term ν
    β   : {ν : Nat} {t : Term (suc ν)} {u : Term ν}
            → app ν (lam ν t) u ≡  ν , (suc ν) ▹ t [ ν , ν < id ν , u > ]
    η   : {ν : Nat} {t : Term ν} → t ≡ lam ν (app (suc ν) ((suc _) , _ ▹ t [ p _ ]) (q ν))
