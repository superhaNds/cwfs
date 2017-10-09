{-# OPTIONS --allow-unsolved-metas #-}
module Unityped.Isomorphism where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; tail ; tabulate)
open import Data.Vec.Properties
open import Data.Fin using (Fin ; zero ; suc)
open import Function renaming (_∘_ to _◯_) using (_$_ ; flip)
open import Unityped.WSModel renaming (_∘_ to _∘'_ ; q to q~ ; id to id~ ; p to p~)
open import Unityped.UcwfModel renaming (_[_] to _`[_])
open import Unityped.Wellscoped.WsUcwf
open import Unityped.Wellscoped.Properties
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqR

-- Translation functions
toCwf : ∀ {n} → WellScopedTm n → CwfTm n
toWs  : ∀ {n} → CwfTm n → WellScopedTm n
toVec : ∀ {m n} → Hom m n → VecTerm m n
toHom : ∀ {m n} → VecTerm m n → Hom m n

toVec (id n)     = id~ n
toVec (ts ∘ us)  = toVec ts ∘' toVec us
toVec (p n)      = p~ n
toVec <>         = empt
toVec < ts , t > = ext (toVec ts) (toWs t)

toHom []       = <>
toHom (x ∷ xs) = < toHom xs , toCwf x >

toWs (q n)       = q~ n
toWs (t `[ ts ]) = toWs t ′[ toVec ts ]
toWs (lam n t)   = lam n (toWs t)
toWs (app n t u) = app n (toWs t) (toWs u)

toCwf (var _ zero)    = q _
toCwf (var _ (suc i)) = weaken (toCwf (var _ i))
toCwf (lam n t)       = lam n (toCwf t)
toCwf (app n t u)     = app n (toCwf t) (toCwf u)

-- Inverses
ws∘ucwf : ∀ {n}   (t : WellScopedTm n) → t ≡ toWs (toCwf t)
vec∘hom : ∀ {m n} (v : Vec (WellScopedTm m) n) → v ≡ toVec (toHom v)
ucwf∘ws : ∀ {n}   (u : CwfTm n) → u ~ₜ toCwf (toWs u)
hom∘vec : ∀ {n m} (u : Hom m n) → u ~ₕ toHom (toVec u)

toHomDist∘ : ∀ {m n k} (xs : Vec (WellScopedTm n) k) (ys : Vec (WellScopedTm m) n)
               → toHom (xs ∘' ys) ~ₕ (toHom xs) ∘ (toHom ys)
               
subCommutes : ∀ {m n} (t : WellScopedTm n) (xs : Vec (WellScopedTm m) n)
                → toCwf (t ′[ xs ]) ~ₜ toCwf t `[ toHom xs ]

ucwf∘ws (q n) = refl~ₜ
ucwf∘ws (u `[ ts ]) = sym~ₜ $ begin
  toCwf (toWs u ′[ toVec ts ])         ≈⟨ subCommutes (toWs u) (toVec ts) ⟩ 
  toCwf (toWs u) `[ toHom (toVec ts) ] ≈⟨ sym~ₜ $ cong~ₜ (λ z → z `[ _ ]) (ucwf∘ws u) ⟩
  u `[ toHom (toVec ts) ]               ≈⟨ sym~ₜ $ congh~ₜ (λ z → _ `[ z ]) (hom∘vec ts) ⟩
  u `[ ts ]                             ∎
  where open EqR (CwfTmS {_})
ucwf∘ws (lam n t) = cong~ₜ (lam n) (ucwf∘ws t)
ucwf∘ws (app n t u) =
  trans~ₜ (cong~ₜ (app n t) (ucwf∘ws u))
          (cong~ₜ (λ z → app n z (toCwf $ toWs u)) (ucwf∘ws t))

hom∘vec (id zero)    = id₀
hom∘vec (id (suc m)) = begin
  id (suc m)             ≈⟨ id<p,q> ⟩
  < p _ , q _ >          ≈⟨ cong~ₕ <_, q _ > (hom∘vec (p m)) ⟩
  < toHom (p~ m) , q _ > ≈⟨ help m ⟩
  _                      ∎
  where open EqR (HomS {_} {_})
        help : ∀ m → < toHom (p~ m) , q m >
                ~ₕ < toHom (tail $ id~ _) , q m >
        help m rewrite tailIdp m = refl~ₕ
          
hom∘vec (ts ∘ us) = sym~ₕ $
  trans~ₕ (trans~ₕ (toHomDist∘ (toVec ts) (toVec us))
                   (cong~ₕ (λ z → z ∘ _) (sym~ₕ $ hom∘vec ts)))
          (cong~ₕ (λ z → _ ∘ z) (sym~ₕ $ hom∘vec us))
          
hom∘vec (p zero) = hom0~<> (p 0)
hom∘vec (p (suc zero)) = begin
  p 1 ≈⟨ eta (p 1) ⟩
  < p 0 ∘ p 1 , q 0 `[ p 1 ] > ≈⟨ cong~ₕ (λ x → < x ∘ p 1 , q 0 `[ p 1 ] >) (hom0~<> (p 0)) ⟩
  < <> ∘ p 1 , q 0 `[ p 1 ] >  ≈⟨ cong~ₕ (<_, q zero `[ p (suc zero) ] >)
                                         (∘<> (p (suc zero))) ⟩
  < <> , q 0 `[ p 1 ] >        ∎
  where open EqR (HomS {_} {_})
hom∘vec (p (suc (suc zero))) = begin
  p 2                                                      ≈⟨ eta $ p 2 ⟩
  < p 1 ∘ p (2) , q 1 `[ p 2 ] >                           ≈⟨ cong~ₕ (λ x → < x ∘ p 2 , q 1 `[ p 2 ] >) (eta $ p 1) ⟩
  < < p 0 ∘ p 1 , q 0 `[ p 1 ] > ∘ p 2 , q 1 `[ p 2 ] >    ≈⟨ cong~ₕ (λ x → < < x , q 0 `[ p 1 ] > ∘ p 2 , q 1 `[ p 2 ] >)
                                                                     (hom0~<> $ p 0 ∘ p 1) ⟩
  < < <> , q 0 `[ p 1 ] > ∘ p 2 , q 1 `[ p 2 ] >           ≈⟨ refl~ₕ ⟩
  < < <> , q 0 `[ p 1 ] > ∘ p 2 , weaken (q 1) >           ≈⟨ cong~ₕ (λ z → < z , q 1 `[ p 2 ] >)
                                                                     (<a,t>∘s (q 0 `[ p 1 ]) <> (p 2)) ⟩
  < < <> ∘ p 2 , q 0 `[ p 1 ] `[ p 2 ] > , weaken (q 1) >  ≈⟨ cong~ₕ (λ z → < < z , (q 0 `[ p 1 ]) `[ p 2 ] > , q 1 `[ p 2 ] >)
                                                                     (∘<> (p 2)) ⟩
  < < <> , q 0 `[ p 1 ] `[ p 2 ] > , weaken (q 1) >        ≈⟨ refl~ₕ ⟩
  < < <> , weaken (weaken $ q 0) > , weaken (q 1) >        ∎
  where open EqR (HomS {_} {_})

hom∘vec (p (suc (suc (suc n)))) = {!!}

hom∘vec <> = refl~ₕ
hom∘vec < u , x > = sym~ₕ $
  trans~ₕ (sym~ₕ $ cong~ₕ (<_, toCwf (toWs x) >) (hom∘vec u))
          (sym~ₕ $ congt~ₕ (< u ,_>) (ucwf∘ws x))
                   
ws∘ucwf (var _ zero) = refl
ws∘ucwf (var _ (suc x)) = sym $
  trans (sym $ cong (_′[ p~ _ ]) (ws∘ucwf (var _ x)))
        (lookupPLemma _ x)
ws∘ucwf (lam n t) = cong (lam n) (ws∘ucwf t)
ws∘ucwf (app n t u) = trans (cong (app n t) (ws∘ucwf u))
                            (cong (λ z → app n z _) (ws∘ucwf t))
                                
vec∘hom [] = refl
vec∘hom (x ∷ xs)
  rewrite sym (vec∘hom xs) |
          sym (ws∘ucwf x) = refl

subCommutes (var _ zero)    (x ∷ xs) = q[<a,t>] (toCwf x) (toHom xs)
subCommutes (var _ (suc i)) (x ∷ xs) = sym~ₜ $ begin
  (toCwf (var _ i) `[ p _ ]) `[ < toHom xs , toCwf x > ]
    ≈⟨ sym~ₜ (∘sub (toCwf (var _ i)) (p _) < toHom xs , toCwf x >) ⟩
  toCwf (var _ i) `[ p _ ∘ < toHom xs , toCwf x > ]
    ≈⟨ sym~ₜ $ congh~ₜ (_`[_] (toCwf $ var _ i)) (p∘<a,t> (toCwf x) (toHom xs)) ⟩
  toCwf (var _ i) `[ toHom xs ] ≈⟨ sym~ₜ $ subCommutes (var _ i) xs ⟩ 
  (toCwf $ var _ i ′[ xs ])     ∎
  where open EqR (CwfTmS {_})
subCommutes (lam n t) xs = begin
  lam _ (toCwf $ t ′[ q~ _ ∷ map lift xs ])     ≈⟨ help ⟩
  lam _ (toCwf $ t ′[ q~ _ ∷ xs ∘' p~ _ ])      ≈⟨ cong~ₜ (lam _) (subCommutes t  (q~ _ ∷ xs ∘' p~ _)) ⟩
  lam _ (toCwf t `[ < toHom (xs ∘' p~ _) , q _ > ])
    ≈⟨ congh~ₜ (λ x → lam _ (toCwf t `[ < x , q _ > ])) {!!} ⟩ -- toHomDist∘ xs (p~ _)
  lam _ (toCwf t `[ < toHom xs ∘ toHom (p~ _) , q _ > ])
    ≈⟨ congh~ₜ (λ x → lam _ (toCwf t `[ < toHom xs ∘ x , q _ > ])) {!!} ⟩ -- hom∘vec p
  lam _ (toCwf t `[ < toHom xs ∘ p _ , q _ > ]) ≈⟨ sym~ₜ (lamCm (toCwf t) (toHom xs)) ⟩ 
  lam _ (toCwf t) `[ toHom xs ]                 ∎
  where open EqR (CwfTmS {_})
        help : lam _ (toCwf $ t ′[ q~ _ ∷ map lift xs ]) ~ₜ
               lam _ (toCwf $  t ′[ q~ _ ∷ xs ∘' p~ _ ])
        help rewrite lift∘p xs = refl~ₜ
subCommutes (app n t u) xs = begin
  app _ (toCwf (t ′[ xs ])) (toCwf (u ′[ xs ]))         ≈⟨ cong~ₜ (flip (app _) (toCwf (u ′[ xs ]))) (subCommutes t xs) ⟩
  app _ (toCwf t `[ toHom xs ]) (toCwf (u ′[ xs ]))     ≈⟨ cong~ₜ (app _ (toCwf t `[ toHom xs ])) (subCommutes u xs) ⟩
  app _ (toCwf t `[ toHom xs ]) (toCwf u `[ toHom xs ]) ≈⟨ appCm (toCwf t) (toCwf u) (toHom xs) ⟩
  app _ (toCwf t) (toCwf u) `[ toHom xs ]               ∎
  where open EqR (CwfTmS {_})

toHomDist∘ []       ys = sym~ₕ $ ∘<> (toHom ys)
toHomDist∘ (x ∷ xs) ys = sym~ₕ $  begin
<<<<<<< HEAD
  < toHom xs , toCwf x > ∘ toHom ys               ≈⟨ <a,t>∘s (toCwf x) (toHom xs) (toHom ys) ⟩
  < toHom xs ∘ toHom ys , toCwf x `[ toHom ys ] > ≈⟨ cong~ₕ (λ z → < z , _ >) (sym~ₕ $ toHomDist∘ xs ys) ⟩
  < toHom (xs ∘' ys) , toCwf x `[ toHom ys ] >    ≈⟨ congt~ₕ (λ z → < _ , z >) (sym~ₜ $ subCommutes x ys) ⟩
  < toHom (xs ∘' ys) , toCwf (x ′[ ys ]) >        ∎
  where open EqR (HomS {_} {_})
