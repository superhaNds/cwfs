module Unityped.Ucwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Ucwf (Term : Nat → Set) : Set₁ where
  private
    Hom : Nat → Nat → Set
    Hom μ ν = Vec (Term μ) ν
  field
    id     : (ν : Nat) → Hom ν ν
    <>     : {μ : Nat} → Hom μ 0
    p      : (ν : Nat) → Hom (suc ν) ν
    q      : (ν : Nat) → Term (suc ν)
    _∘_    : {μ ν k : Nat} → Hom ν k → Hom μ ν → Hom μ k
    _[_]   : {μ ν : Nat} → Term ν → Hom μ ν → Term μ
    <_,_>  : {μ ν : Nat} → Hom μ ν → Term μ → Hom μ (suc ν)

    id₀      : id 0 ≡ <>
    ∘<>      : ∀ {μ ν : Nat} (ts : Hom μ ν) → <> ∘ ts ≡ <> 
    id<p,q>  : ∀ {ν : Nat} → id (suc ν) ≡ < p ν , q ν >
    ∘lid     : ∀ {μ ν : Nat} (ts : Hom μ ν) → id ν ∘ ts ≡ ts
    ∘rid     : ∀ {μ ν : Nat} (ts : Hom μ ν) → ts ∘ id μ ≡ ts
    ∘asso    : ∀ {μ ν k p : Nat} (ts : Hom ν k) (us : Hom μ ν) (vs : Hom p μ)
                 → (ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)
    subid    : ∀ {μ ν : Nat} (t : Term ν) → t [ id ν ] ≡ t
    p∘<γ,α>  : ∀ {μ ν k : Nat} → (t : Term ν) → (ts : Hom ν k) → p k ∘ < ts , t > ≡ ts
    q[<γ,α>] : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν μ) → q μ [ < ts , t > ] ≡ t
    ∘inSub   : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν ν) (us : Hom μ ν)
                 → t [ ts ∘  us ] ≡ (t [ ts ]) [ us ]
    <δ,α>∘γ  : ∀ {μ ν : Nat} (t : Term ν) (ts : Hom ν μ) (us : Hom μ ν)
                 → < ts , t > ∘ us ≡ < ts ∘ us , t [ us ] >

record λβ-ucwf (Term : Nat → Set) : Set₁ where
  private
    Hom : Nat → Nat → Set
    Hom μ ν = Vec (Term μ) ν
  field
    ucwf : Ucwf Term
  open Ucwf ucwf public
  field
    lam   : (ν : Nat) → Term (suc ν) → Term ν
    app   : (ν : Nat) → Term ν → Term ν → Term ν
    β     : {ν : Nat} (t : Term (suc ν)) (u : Term ν) → app ν (lam ν t) u ≡  t [ < id ν , u > ]
    η     : {ν : Nat} (t : Term ν) → lam ν (app (suc ν) (t [ p ν ]) (q ν)) ≡ t
    appCm : {ν μ : Nat} (t u : Term ν) (ts : Hom μ ν) → app μ (t [ ts ]) (u [ ts ]) ≡ app ν t u [ ts ]
    lamCm : {ν μ : Nat} (t : Term (suc ν)) (ts : Hom μ ν) → lam ν t [ ts ] ≡ lam μ (t [ < ts ∘ p μ , q μ > ])
