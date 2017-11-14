module SimpTyped.Scwf where

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
    ∘<>   : ∀ {Γ Δ} (γ : Hom Γ Δ) → <> ∘ γ ~~ <>
    varp  : ∀ {Γ α} → id {Γ , α} ~~ < p , q > 
    idL   : ∀ {Γ Δ} (γ : Hom Δ Γ) → id ∘ γ ~~ γ
    idR   : ∀ {Γ Δ} (γ : Hom Γ Δ) → γ ∘ id ~~ γ
    assoc : ∀ {Γ Δ Θ Λ} (γ : Hom Δ Θ) (δ : Hom Γ Δ) (ζ : Hom Λ Γ) →
            (γ ∘ δ) ∘ ζ ~~ γ ∘ (δ ∘ ζ)
    tmId  : ∀ {Γ α} (t : Tm Γ α) → t [ id ] ~ t
    pCons : ∀ {Δ Θ α} (t : Tm Δ α) (γ : Hom Δ Θ) → p ∘ < γ , t > ~~ γ
    q[]   : ∀ {Γ Δ α} (t : Tm Γ α) (γ : Hom Γ Δ) → q [ < γ , t > ] ~ t
    clos  : ∀ {Γ Δ Θ α} (t : Tm Δ α) (γ : Hom Γ Δ) (δ : Hom Θ Γ) →
            t [ γ ∘ δ ] ~ t [ γ ] [ δ ]
    maps  : ∀ {Γ Δ α} (t : Tm Δ α) (γ : Hom Δ Γ) (δ : Hom Γ Δ) →
            < γ , t > ∘ δ ~~ < γ ∘ δ , t [ δ ] >
    cong-[] : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Hom Δ Γ} →
               t ~ t' → γ ~~ γ' → t [ γ ] ~ t' [ γ' ]
    cong-<,> : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Hom Γ Δ} →
               t ~ t' → γ ~~ γ' → < γ , t > ~~ < γ' , t' >
    cong-∘ : ∀ {Γ Δ Θ} {γ δ : Hom Δ Θ} {γ' δ' : Hom Γ Δ} →
             γ ~~ δ → γ' ~~ δ' → γ ∘ γ' ~~ δ ∘ δ'
