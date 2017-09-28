{-# OPTIONS --allow-unsolved-metas #-}
module Unityped.ModelIsomorphism where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_] ; tabulate ; head ; tail)
open import Data.Vec.Properties using (lookup∘tabulate ; lookup-allFin)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_$_ ; flip)
open import Unityped.WSModel renaming (_∘_ to comp ; _′[_] to sub ; q to qWS ; id to idWS ; p to pWS)
open import Relation.Binary.PropositionalEquality
open import Unityped.UcwfModel renaming (_[_] to _`[_])
import Relation.Binary.EqReasoning as EqR

-- Translation functions
toUcwf   : ∀ {n} → WellScopedTm n → UcwfTm n
toWs     : ∀ {n} → UcwfTm n → WellScopedTm n
toVec    : ∀ {m n} → HomCwf m n → Vec (WellScopedTm m) n
toHom    : ∀ {m n} → Vec (WellScopedTm m) n → HomCwf m n

toVec (id n)     = idWS n
toVec (ts ∘ us)  = comp (toVec ts) (toVec us) 
toVec (p n)      = pWS n
toVec <>         = empt
toVec < ts , t > = ext (toVec ts) (toWs t)

toHom []       = <>
toHom (x ∷ xs) = < toHom xs , toUcwf x >

toWs (q n)       = qWS n
toWs (t `[ ts ]) = sub (toWs t) (toVec ts)
toWs (lam n t)   = lam n (toWs t)
toWs (app n t u) = app n (toWs t) (toWs u)

toUcwf (var _ zero)    = q _
toUcwf (var _ (suc i)) = weaken (toUcwf (var _ i))
toUcwf (lam n t)       = lam n (toUcwf t)
toUcwf (app n t u)     = app n (toUcwf t) (toUcwf u)

-- Inverses
ws∘ucwf : ∀ {n}   (t : WellScopedTm n) → t ≡ toWs (toUcwf t)
vec∘hom : ∀ {m n} (v : Vec (WellScopedTm m) n) → v ≡ toVec (toHom v)
ucwf∘ws : ∀ {n}   (u : UcwfTm n) → u ~ₜ toUcwf (toWs u)
hom∘vec : ∀ {n m} (u : HomCwf m n) → u ~ₕ toHom (toVec u)

toHomDist∘ : ∀ {m n k} (xs : Vec (WellScopedTm n) k) (ys : Vec (WellScopedTm m) n)
               → toHom (comp xs ys) ~ₕ (toHom xs) ∘ (toHom ys)
               
subCommutes : ∀ {m n} (t : WellScopedTm n) (xs : Vec (WellScopedTm m) n)
                → toUcwf (sub t xs) ~ₜ toUcwf t `[ toHom xs ]

ucwf∘ws (q n) = refl~ₜ
ucwf∘ws (u `[ ts ]) = sym~ₜ $
  begin
    toUcwf (sub (toWs u) (toVec ts))
  ≈⟨ subCommutes (toWs u) (toVec ts) ⟩ 
    toUcwf (toWs u) `[ toHom (toVec ts) ]
  ≈⟨ sym~ₜ $ cong~ₜ (λ z → z `[ _ ]) (ucwf∘ws u) ⟩
    u `[ toHom (toVec ts) ]
  ≈⟨ sym~ₜ $ congh~ₜ (λ z → _ `[ z ]) (hom∘vec ts) ⟩
    u `[ ts ]
  ∎ where open EqR (UcwfTmS {_})
ucwf∘ws (lam n t) = cong~ₜ (lam n) (ucwf∘ws t)
ucwf∘ws (app n t u) =
  trans~ₜ (cong~ₜ (app n t) (ucwf∘ws u))
          (cong~ₜ (λ z → app n z (toUcwf $ toWs u)) (ucwf∘ws t))

hom∘vec (id zero)    = id₀
hom∘vec (id (suc m)) =
  begin
    id (suc m)
  ≈⟨ id<p,q> ⟩
    < p _ , q _ >
  ≈⟨ cong~ₕ <_, q _ > (hom∘vec (p m)) ⟩
    < toHom (pWS m) , q _ >
  ≈⟨ help m ⟩
    < toHom $ tail (idWS _) , q _ >
  ∎ where open EqR (HomCwfS {_} {_})
          help : ∀ m → < toHom (pWS m) , q m >
                         ~ₕ < toHom (tail $ idWS _) , q m >
          help m rewrite tailIdp m = refl~ₕ
hom∘vec (ts ∘ us) = sym~ₕ $
  trans~ₕ (trans~ₕ (toHomDist∘ (toVec ts) (toVec us))
                   (cong~ₕ (λ z → z ∘ _) (sym~ₕ $ hom∘vec ts)))
          (cong~ₕ (λ z → _ ∘ z) (sym~ₕ $ hom∘vec us))
hom∘vec (p zero) = hom0~<> $ p zero
hom∘vec (p (suc n)) = sym~ₕ $
  begin
    < toHom (tail $ pWS (1 + n)) , weaken (q n) >
  ≈⟨ help ⟩
    < toHom (comp (pWS n) (pWS (1 + n))) , weaken $ q n >
  ≈⟨ cong~ₕ (λ x → < x , weaken $ q n >) (toHomDist∘ (pWS n) (pWS $ 1 + n)) ⟩
    < toHom (pWS n) ∘ toHom (pWS (1 + n)) , weaken $ q n >
  ≈⟨ cong~ₕ (λ x → < x ∘ toHom (pWS (1 + n)) , weaken $ q n >) (sym~ₕ (hom∘vec (p n))) ⟩ 
    < p n ∘ toHom (pWS (1 + n)) , q n `[ p (1 + n) ] >
  ≈⟨ {!!} ⟩ 
    p (1 + n)
  ∎ where open EqR (HomCwfS {_} {_})
          help : < toHom (tail $ pWS (suc n)) , weaken (q n) > ~ₕ
                 < toHom (comp (pWS n) (pWS (suc n))) , weaken $ q n >
          help rewrite tailComp n = refl~ₕ
hom∘vec <> = refl~ₕ
hom∘vec < u , x > = sym~ₕ $
  trans~ₕ (sym~ₕ $ cong~ₕ (<_, toUcwf (toWs x) >) (hom∘vec u))
          (sym~ₕ $ congt~ₕ (< u ,_>) (ucwf∘ws x))

ws∘ucwf (var _ zero) = refl
ws∘ucwf (var _ (suc x)) = sym $
  trans (sym $ cong (flip sub (pWS _)) (ws∘ucwf (var _ x)))
        (lookupPLemma _ x)
ws∘ucwf (lam n t) = cong (lam n) (ws∘ucwf t)
ws∘ucwf (app n t u) = trans (cong (app n t) (ws∘ucwf u))
                            (cong (λ z → app n z _) (ws∘ucwf t))
                                
vec∘hom [] = refl
vec∘hom (x ∷ xs)
  rewrite sym (vec∘hom xs) |
          sym (ws∘ucwf x) = refl

subCommutes (var _ zero)    (x ∷ xs) = q[<a,t>] (toUcwf x) (toHom xs)
subCommutes (var _ (suc i)) (x ∷ xs) = sym~ₜ $
  begin
    (toUcwf (var _ i) `[ p _ ]) `[ < toHom xs , toUcwf x > ]
  ≈⟨ sym~ₜ (∘sub (toUcwf (var _ i)) (p _) < toHom xs , toUcwf x >) ⟩
    toUcwf (var _ i) `[ p _ ∘ < toHom xs , toUcwf x > ]
  ≈⟨ sym~ₜ $ congh~ₜ (_`[_] (toUcwf $ var _ i))
                     (p∘<a,t> (toUcwf x) (toHom xs)) ⟩
    toUcwf (var _ i) `[ toHom xs ]
  ≈⟨ sym~ₜ $ subCommutes (var _ i) xs ⟩ 
    (toUcwf $ sub (var _ i) xs)
  ∎ where open EqR (UcwfTmS {_})
subCommutes (lam n t) xs =  
  begin
    lam _ (toUcwf $ sub t (qWS _ ∷ map lift xs))
  ≈⟨ help ⟩
    lam _ (toUcwf $ sub t (qWS _ ∷ comp xs (pWS _)))
  ≈⟨ cong~ₜ (lam _) (subCommutes t  (qWS _ ∷ comp xs (pWS _))) ⟩
    lam _ (toUcwf t `[ < toHom (comp xs (pWS _)) , q _ > ])
  ≈⟨ congh~ₜ (λ x → lam _ (toUcwf t `[ < x , q _ > ])) {!!} ⟩
    lam _ (toUcwf t `[ < toHom xs ∘ toHom (pWS _) , q _ > ])
  ≈⟨ congh~ₜ (λ x → lam _ (toUcwf t `[ < toHom xs ∘ x , q _ > ])) {!!} ⟩
    lam _ (toUcwf t `[ < toHom xs ∘ p _ , q _ > ])
  ≈⟨ sym~ₜ (lamCm (toUcwf t) (toHom xs)) ⟩ 
    lam _ (toUcwf t) `[ toHom xs ]
  ∎ where open EqR (UcwfTmS {_})
          help : lam _ (toUcwf $ sub t (qWS _ ∷ map lift xs)) ~ₜ
                  lam _ (toUcwf $ sub t (qWS _ ∷ comp xs (pWS _)))
          help rewrite lift∘p xs = refl~ₜ
subCommutes (app n t u) xs =
  begin
    app _ (toUcwf (sub t xs)) (toUcwf (sub u xs))
  ≈⟨ cong~ₜ (λ z → app _ z (toUcwf (sub u xs))) (subCommutes t xs) ⟩
    app _ (toUcwf t `[ toHom xs ]) (toUcwf (sub u xs))
  ≈⟨ cong~ₜ (app _ (toUcwf t `[ toHom xs ])) (subCommutes u xs) ⟩
    app _ (toUcwf t `[ toHom xs ]) (toUcwf u `[ toHom xs ])
  ≈⟨ appCm (toUcwf t) (toUcwf u) (toHom xs) ⟩
    app _ (toUcwf t) (toUcwf u) `[ toHom xs ]
  ∎ where open EqR (UcwfTmS {_})

toHomDist∘ []       ys = sym~ₕ $ ∘<> (toHom ys)
toHomDist∘ (x ∷ xs) ys = sym~ₕ $
  begin
    < toHom xs , toUcwf x > ∘ toHom ys
  ≈⟨ <a,t>∘s (toUcwf x) (toHom xs) (toHom ys) ⟩
    < toHom xs ∘ toHom ys , toUcwf x `[ toHom ys ] >
  ≈⟨ cong~ₕ (λ z → < z , _ >) (sym~ₕ $ toHomDist∘ xs ys) ⟩
    < toHom (comp xs ys) , toUcwf x `[ toHom ys ] >
  ≈⟨ congt~ₕ (λ z → < _ , z >) (sym~ₜ $ subCommutes x ys) ⟩
    < toHom (comp xs ys) , toUcwf (sub x ys) >
  ∎ where open EqR (HomCwfS {_} {_})
