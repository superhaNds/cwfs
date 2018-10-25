-------------------------------------------------------------------------
-- A proof of isomorphism between a intrinsically typed scwf and the
-- extrinsic scwf. Both based on well-scoped terms.
-------------------------------------------------------------------------
module ExtSimpTyped.IsoIntExt where

open import Unityped.ExpSubLam
  renaming (_~_ to _~'_ ; _≈_ to _≈'_
           ; refl~ to refl~' ; refl≈ to refl≈'
           ; Tm to RTm ; Sub to RSub
           )
open import ExtSimpTyped.ExpSubLam
open import ExtSimpTyped.IntExpSubLam
open import ExtSimpTyped.CtxType
open import Data.Product using (Σ ; _,_)

strip   : ∀ {n} {Γ : Ctx n} {α} → Tm Γ α → RTm n

strip▹  : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} → Sub Δ Γ → RSub m n

typing  : ∀ {n} {Γ : Ctx n} {α} (t : Tm Γ α) → Γ ⊢ strip t ∈ α

typing▹ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (ρ : Sub Δ Γ) → Γ ⊢ strip▹ ρ ∈s Δ

strip q         = q
strip (t [ γ ]) = strip t [ strip▹ γ ]
strip (app t u) = app (strip t) (strip u)
strip (lam t)   = ƛ (strip t)

strip▹ <>        = <>
strip▹ id        = id
strip▹ p         = p
strip▹ (γ₁ ∘ γ₂) = strip▹ γ₁ ∘ strip▹ γ₂
strip▹ < γ , t > = < strip▹ γ , strip t >

typing q         = ⊢q
typing (t [ γ ]) = ⊢sub (typing t) (typing▹ γ)
typing (app t u) = ⊢app (typing t) (typing u)
typing (lam t)   = ⊢ƛ (typing t)

typing▹ <>        = ⊢<>
typing▹ id        = ⊢id
typing▹ p         = ⊢p
typing▹ (γ₁ ∘ γ₂) = ⊢∘ (typing▹ γ₁) (typing▹ γ₂)
typing▹ < γ , t > = ⊢<,> (typing t) (typing▹ γ)

join  : ∀ {n Γ α} → Σ (RTm n) (Γ ⊢_∈ α) → Tm Γ α

join▹ : ∀ {m n Γ Δ} → Σ (RSub m n) (Γ ⊢_∈s Δ) → Sub Δ Γ

join (q       , ⊢q)         = q
join (t [ γ ] , ⊢sub ⊢t ⊢γ) = (join (t , ⊢t)) [ join▹ (γ , ⊢γ) ]
join (app t u , ⊢app ⊢t ⊢u) = app (join (t , ⊢t)) (join (u , ⊢u))
join (ƛ t     , ⊢ƛ ⊢t)      = lam (join (t , ⊢t))

join▹ (id        , ⊢id)        = id
join▹ (γ₁ ∘ γ₂   , ⊢∘ ⊢γ₁ ⊢γ₂) = (join▹ (γ₁ , ⊢γ₁)) ∘ join▹ (γ₂ , ⊢γ₂)
join▹ (p         , ⊢p)         = p
join▹ (<>        , ⊢<>)        = <>
join▹ (< γ , t > , ⊢<,> ⊢t ⊢γ) = < join▹ (γ , ⊢γ) , join (t , ⊢t) >

joinstrip▹ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} (γ : Sub Δ Γ) 
             → join▹ (strip▹ γ , typing▹ γ) ≈ γ

joinstrip : ∀ {n α} {Γ : Ctx n} (t : Tm Γ α)
            → join (strip t , typing t) ~ t

stripjoin▹ : ∀ {m n Γ Δ} (γ : RSub m n) (⊢γ : Γ ⊢ γ ∈s Δ)
             → strip▹ (join▹ (γ , ⊢γ)) ≈' γ

stripjoin : ∀ {n Γ α} (t : RTm n) (⊢t : Γ ⊢ t ∈ α)
            → strip (join (t , ⊢t)) ~' t

--joineq : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (t t' : Tm Γ α) → t ~' t' → join (strip t , typing t) ~ join 

joinstrip q         = refl~
joinstrip (t [ γ ]) = cong-sub (joinstrip t) (joinstrip▹ γ)
joinstrip (app t u) = cong-app (joinstrip t) (joinstrip u)
joinstrip (lam t)   = cong-lam (joinstrip t)

joinstrip▹ <>        = refl≈
joinstrip▹ id        = refl≈
joinstrip▹ p         = refl≈
joinstrip▹ (γ₁ ∘ γ₂) = cong-∘ (joinstrip▹ γ₁) (joinstrip▹ γ₂)
joinstrip▹ < γ , t > = cong-<,> (joinstrip t) (joinstrip▹ γ)

stripjoin q          ⊢q          = refl~'
stripjoin (t [ γ ]) (⊢sub ⊢t ⊢γ) = cong-sub (stripjoin t ⊢t) (stripjoin▹ γ ⊢γ)
stripjoin (app t u) (⊢app ⊢t ⊢u) = cong-app (stripjoin t ⊢t) (stripjoin u ⊢u)
stripjoin (ƛ t)     (⊢ƛ ⊢t)      = cong-lam (stripjoin t ⊢t)

stripjoin▹ id        ⊢id          = refl≈'
stripjoin▹ (γ₁ ∘ γ₂) (⊢∘ ⊢γ₁ ⊢γ₂) = cong-∘ (stripjoin▹ γ₁ ⊢γ₁) (stripjoin▹ γ₂ ⊢γ₂)
stripjoin▹ p         ⊢p           = refl≈'
stripjoin▹ <>        ⊢<>          = refl≈'
stripjoin▹ < γ , t > (⊢<,> ⊢t ⊢γ) = cong-<,> (stripjoin t ⊢t) (stripjoin▹ γ ⊢γ)

stripeq : ∀ {n} {Γ : Ctx n} {α} {t t' : Tm Γ α} → t ~ t' → strip t ~' strip t'

strip▹eq : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {γ γ' : Sub Δ Γ} → γ ≈ γ' → strip▹ γ ≈' strip▹ γ'

stripeq (subId t)         = subId
stripeq (qCons t ρ)       = q-sub
stripeq (subComp t ρ σ)   = subComp
stripeq (subApp t u ρ)    = sym~ subApp
stripeq (subLam t ρ)      = subLam
stripeq (cong-sub eq γ≈γ) = cong-sub (stripeq eq) (strip▹eq γ≈γ)
stripeq (cong-app eq eq₁) = cong-app (stripeq eq) (stripeq eq₁)
stripeq (cong-lam eq)     = cong-lam (stripeq eq)
stripeq (sym~ eq)         = sym~ (stripeq eq)
stripeq (trans~ eq₁ eq₂)  = trans~ (stripeq eq₁) (stripeq eq₂)

strip▹eq id-zero          = id-zero
strip▹eq (left-zero ρ)    = left-zero
strip▹eq idExt            = idExt
strip▹eq (idL ρ)          = idL
strip▹eq (idR ρ)          = idR
strip▹eq (assoc ρ σ τ)    = ∘-asso
strip▹eq (pCons t ρ)      = p-∘
strip▹eq (compExt t ρ σ)  = compExt
strip▹eq (cong-<,> x eq)  = cong-<,> (stripeq x) (strip▹eq eq)
strip▹eq (cong-∘ eq₁ eq₂) = cong-∘ (strip▹eq eq₁) (strip▹eq eq₂)
strip▹eq (sym≈ eq)        = sym≈ (strip▹eq eq)
strip▹eq (trans≈ eq₁ eq₂) = trans≈ (strip▹eq eq₁) (strip▹eq eq₂)

prop : ∀ {n} {Γ : Ctx n} {α} {t t'} → t ~' t' → Γ ⊢ t ∈ α → Γ ⊢ t' ∈ α
prop q-sub ⊢t = {!!}
prop subId ⊢t = {!!}
prop subComp ⊢t = {!!}
prop subApp ⊢t = {!!}
prop subLam ⊢t = {!!}
prop β ⊢t = {!!}
prop η ⊢t = {!!}
prop (cong-sub eq x) ⊢t = {!!}
prop (cong-app eq eq₁) ⊢t = {!!}
prop (cong-lam eq) ⊢t = {!!}
prop (sym~ eq) ⊢t = {!!}
prop (trans~ eq eq₁) ⊢t = {!!}

e : ∀ {n} {Γ : Ctx n} {α} {t t'}
    (eq : t ~' t')
    (⊢t : Γ ⊢ t ∈ α)
    (⊢t' : Γ ⊢ t' ∈ α) → join (t , ⊢t) ~ join (t' , ⊢t')
e q-sub ⊢t ⊢t' = {!qCons!}
e subId ⊢t ⊢t' = {!!}
e subComp ⊢t ⊢t' = {!!}
e subApp ⊢t ⊢t' = {!!}
e subLam ⊢t ⊢t' = {!!}
e β ⊢t ⊢t' = {!!}
e η ⊢t ⊢t' = {!!}
e (cong-sub eq x) ⊢t ⊢t' = {!cong-sub!}
e (cong-app eq eq₁) ⊢t ⊢t' = {!!}
e (cong-lam eq) ⊢t ⊢t' = {!!}
e (sym~ eq) ⊢t ⊢t' = sym~ (e eq ⊢t' ⊢t)
e (trans~ eq eq₁) ⊢t ⊢t' = {!!}
