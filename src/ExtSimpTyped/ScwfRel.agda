-------------------------------------------------------------------------
-- A proof of isomorphism between the directly typed scwf and the
-- extrinsic scwf version based on raw terms with typing rules
-------------------------------------------------------------------------
module ExtSimpTyped.ScwfRel where

open import ExtSimpTyped.ScwfExt
  renaming (_≈_ to _≈'_ ; _≋_ to _≋'_ ;
            refl≈ to refl≈' ; refl≋ to refl≋')
open import ExtSimpTyped.ScwfInt
open import ExtSimpTyped.CtxType
open import Data.Product using (Σ ; _,_)

-------------------------------------------------------------------------
-- Translation functions between scwfs of explicit substitutions

-- Strips types from a typed term back to a raw term

strip  : ∀ {n} {Γ : Ctx n} {α} → Tm Γ α → RTm n

-- strip for substitutions

strip▹ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} → Sub Δ Γ → RSub n m

-- Given a typed term, returns an element of the typing relation on the raw term

typing  : ∀ {n} {Γ : Ctx n} {α} (t : Tm Γ α) → Γ ⊢ strip t ∈ α

-- typing for substitutions

typing▹ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (ρ : Sub Δ Γ) → Δ ▹ Γ ⊢ strip▹ ρ

strip q         = q
strip (t [ ρ ]) = strip t [ strip▹ ρ ]
strip (app t u) = app (strip t) (strip u)
strip (lam t)   = lam (strip t)

strip▹ <>        = <>
strip▹ id        = id
strip▹ p         = p
strip▹ (ρ ∘ σ)   = strip▹ ρ ∘ strip▹ σ
strip▹ < ρ , t > = < strip▹ ρ , strip t >

typing q         = q∈ 
typing (t [ ρ ]) = sub∈  (typing t) (typing▹ ρ)
typing (app t u) = app∈ (typing t) (typing u)
typing (lam t)   = lam∈ (typing t)

typing▹ <>        = ⊢<>
typing▹ id        = ⊢id
typing▹ p         = ⊢p
typing▹ (ρ ∘ σ)   = ⊢∘ (typing▹ ρ) (typing▹ σ)
typing▹ < ρ , t > = ⊢<,> (typing t) (typing▹ ρ)

-- Given a dependent pair of a raw term and its typing rule, we get a directly typed term

join  : ∀ {n Γ α} → Σ (RTm n) (Γ ⊢_∈ α) → Tm Γ α

-- join for substitutions

join▹ : ∀ {m n Γ Δ} → Σ (RSub m n) (Δ ▹ Γ ⊢_) → Sub Δ Γ

join (q , q∈)               = q
join (t [ ρ ] , sub∈ t∈ ⊢ρ) = join (t , t∈) [ join▹ (ρ , ⊢ρ) ]
join (app t u , app∈ t∈ u∈) = app (join (t , t∈)) (join (u , u∈))
join (lam t , lam∈ t∈)      = lam (join (t , t∈))

join▹ (<> , ⊢<>)                = <>
join▹ (id , ⊢id)                = id
join▹ (p ,  ⊢p)                 = p
join▹ (< ρ , t > , ⊢<,> t∈  ⊢ρ) = < join▹ (ρ , ⊢ρ) , join (t , t∈) >
join▹ (ρ ∘ σ , ⊢∘ ⊢ρ ⊢σ)        = join▹ (ρ , ⊢ρ) ∘ join▹ (σ , ⊢σ)

-------------------------------------------------------------------------
-- Isomorphism proof

-- Inverse proof signatures
joinstrip▹ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (ρ : Sub Δ Γ)
             → join▹ (strip▹ ρ , typing▹ ρ) ≋ ρ

joinstrip : ∀ {n α} {Γ : Ctx n} (t : Tm Γ α)
            → join (strip t , typing t) ≈ t

stripjoin▹ : ∀ {m n Γ Δ} (ρ : RSub n m) (⊢ρ : Δ ▹ Γ ⊢ ρ)
             → strip▹ (join▹ (ρ , ⊢ρ)) ≋' ρ

stripjoin : ∀ {n Γ α} (t : RTm n) (t∈ : Γ ⊢ t ∈ α)
            → strip (join (t , t∈)) ≈' t

joinstrip▹ <>        = refl≋
joinstrip▹ id        = refl≋
joinstrip▹ p         = refl≋
joinstrip▹ (ρ ∘ σ)   = cong-∘ (joinstrip▹ ρ) (joinstrip▹ σ)
joinstrip▹ < ρ , t > = cong-<,> (joinstrip t) (joinstrip▹ ρ)

joinstrip q         = refl≈
joinstrip (t [ ρ ]) = cong-sub (joinstrip t) (joinstrip▹ ρ)
joinstrip (app t u) = cong-app (joinstrip t) (joinstrip u)
joinstrip (lam t)   = cong-lam (joinstrip t)

stripjoin▹ <> ⊢<>                 = refl≋'
stripjoin▹ id ⊢id                 = refl≋'
stripjoin▹ p  ⊢p                  = refl≋'
stripjoin▹ < ρ , t > (⊢<,> t∈ ⊢ρ) = cong-<,> (stripjoin t t∈) (stripjoin▹ ρ ⊢ρ)
stripjoin▹ (ρ ∘ σ)   (⊢∘ ⊢ρ ⊢σ)   = cong-∘ (stripjoin▹ ρ ⊢ρ) (stripjoin▹ σ ⊢σ)

stripjoin q q∈                   = refl≈'
stripjoin (t [ ρ ]) (sub∈ t∈ ⊢ρ) = cong-sub (stripjoin t t∈) (stripjoin▹ ρ ⊢ρ)
stripjoin (app t u) (app∈ t∈ u∈) = cong-app (stripjoin t t∈) (stripjoin u u∈)
stripjoin (lam t)   (lam∈ t∈)    = cong-lam (stripjoin t t∈)
