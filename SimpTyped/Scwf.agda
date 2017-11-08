module Scwf where



open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Relation.Binary

record Scwf : Set₁ where
  infix 5 _~_
  infix 5 _~~_
  infix 8 _∘_
  field
    Ty  : Set
    Ctx : Set
    _,_ : Ctx → Ty → Ctx
    ε   : Ctx
    Tm  : Ctx → Ty → Set
    Hom : Ctx → Ctx → Set

    _~_  : ∀ {Γ α} → Rel (Tm Γ α) lzero
    _~~_ : ∀ {Γ Δ} → Rel (Hom Γ Δ) lzero

    <>    : ∀ {Γ}     → Hom Γ ε
    id    : ∀ {Γ}     → Hom Γ Γ
    p     : ∀ {Γ α}   → Hom (Γ , α) Γ
    q     : ∀ {Γ α}   → Tm (Γ , α) α
    _∘_   : ∀ {Γ Δ Θ} → Hom Γ Θ → Hom Δ Γ → Hom Δ Θ
    _[_]  : ∀ {Γ Δ α} → Tm Γ α  → Hom Δ Γ → Tm Δ α
    <_,_> : ∀ {Γ Δ α} → Hom Γ Δ → Tm Γ α  → Hom Γ (Δ , α)

    id₀   : id {ε} ~~ <>
    ∘<>   : ∀ {Γ Δ} (ts : Hom Γ Δ) → <> ∘ ts ~~ <>
    varp  : ∀ {Γ α} → id {Γ , α} ~~ < p , q > 
    idL   : ∀ {Γ Δ} (ts : Hom Δ Γ) → id ∘ ts ~~ ts
    idR   : ∀ {Γ Δ} (ts : Hom Γ Δ) → ts ∘ id ~~ ts
    assoc : ∀ {Γ Δ Θ Λ} (ts : Hom Δ Θ) (us : Hom Γ Δ) (vs : Hom Λ Γ) →
            (ts ∘ us) ∘ vs ~~ ts ∘ (us ∘ vs)
    tmId  : ∀ {Γ α} (t : Tm Γ α) → t [ id ] ~ t
    pCons : ∀ {Δ Θ α} (t : Tm Δ α) (ts : Hom Δ Θ) → p ∘ < ts , t > ~~ ts
    q[]   : ∀ {Γ Δ α} (t : Tm Γ α) (ts : Hom Γ Δ) → q [ < ts , t > ] ~ t
    clos  : ∀ {Γ Δ Θ α} (t : Tm Δ α) (ts : Hom Γ Δ) (us : Hom Θ Γ) →
            t [ ts ∘ us ] ~ t [ ts ] [ us ]
    maps  : ∀ {Γ Δ α} (t : Tm Δ α) (ts : Hom Δ Γ) (us : Hom Γ Δ) →
            < ts , t > ∘ us ~~ < ts ∘ us , t [ us ] >
