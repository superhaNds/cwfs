module Unityped.Wellscoped.Typed.ScwfRel where

open import Unityped.Wellscoped.Typed.ScwfComb renaming (Subst to RSubst)
open import Unityped.Wellscoped.Typed.ScwfDirectComb
open import Unityped.Wellscoped.Typed.CtxType
open import Data.Product using (Σ ; _,_)

strip  : ∀ {n} {Γ : Ctx n} {α} → Tm Γ α → RTm n
strip▹ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} → Subst Δ Γ → RSubst n m

strip q         = q
strip (t [ ρ ]) = strip t [ strip▹ ρ ]

strip▹ <>        = <>
strip▹ id        = id
strip▹ p         = p
strip▹ (ρ ∘ σ)   = strip▹ σ ∘ strip▹ ρ
strip▹ < ρ , t > = < strip▹ ρ , strip t >

typing  : ∀ {n} {Γ : Ctx n} {α} (t : Tm Γ α) → Γ ⊢ (strip t) ∈ α
typing▹ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (ρ : Subst Δ Γ) → Δ ▹ Γ ⊢ strip▹ ρ 

typing q         = ⊢q 
typing (t [ x ]) = []∈ (typing t) (typing▹ x)

typing▹ <>        = ⊢<>
typing▹ id        = ⊢id
typing▹ p         = ⊢p
typing▹ (ρ ∘ σ)   = ⊢∘ (typing▹ ρ) (typing▹ σ)
typing▹ < ρ , t > = ⊢<,> (typing t) (typing▹ ρ)

-- (strip, typing) ≅ join

-- strip (join (t,p) ~ t
-- join (strip t, typing t) ~ t

join  : ∀ {n} {Γ : Ctx n} {α} → Σ (RTm n) (Γ ⊢_∈ α) → Tm Γ α
join▹ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} → Σ (RSubst m n) (Δ ▹ Γ ⊢_) →
        Subst Δ Γ

join (q , ⊢q)                = q
join ((t [ ρ ]) , []∈ t∈ ⊢ρ) = (join (t , t∈)) [ join▹ (ρ , ⊢ρ) ]

join▹ (<> , ⊢<>)                = <>
join▹ (id , ⊢id)                = id
join▹ (p ,  ⊢p)                 = p
join▹ (< ρ , t > , ⊢<,> t∈  ⊢ρ) = < (join▹ (ρ , ⊢ρ)) , join (t , t∈) >
join▹ ((ρ ∘ σ) , ⊢∘ ⊢σ ⊢ρ)      = (join▹ (σ , ⊢σ)) ∘ join▹ (ρ , ⊢ρ)
