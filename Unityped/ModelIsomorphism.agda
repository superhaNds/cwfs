module Unityped.ModelIsomorphism where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_] ; tabulate ; head ; tail)
open import Data.Vec.Properties using (lookup∘tabulate ; lookup-allFin)
open import Data.Fin using (Fin ; zero ; suc ; raise ; fromℕ)
open import Function using (_$_ ; flip)
open import Unityped.WSModel
  renaming (q to qWS ; comp to compWS ; sub to subWS ; id to idWS)
open import Relation.Binary.PropositionalEquality
open import Util
open import Unityped.UcwfModel renaming (_[_] to _`[_])
import Relation.Binary.EqReasoning as EqR

-- Translation functions
toUcwf   : ∀ {n} → WellScopedTm n → UcwfTm n
toWs     : ∀ {n} → UcwfTm n → WellScopedTm n
toVec    : ∀ {m n} → HomCwf m n → Vec (WellScopedTm m) n
toHom    : ∀ {m n} → Vec (WellScopedTm m) n → HomCwf m n

toVec (id n)      = idSub n
toVec (hnk ∘ hmn) = compWS (toVec hnk) (toVec hmn) 
toVec (p n)       = projSub n
toVec <>          = empt
toVec < h , t >   = ext (toVec h) (toWs t)

toHom []       = <>
toHom (x ∷ xs) = < toHom xs , toUcwf x >

toWs (q n)       = qWS n
toWs (t `[ h ])  = subWS (toWs t) (toVec h)
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

toUcwfDistSub : ∀ {m n} (t : WellScopedTm n) (xs : Vec (WellScopedTm m) n)
                  → toUcwf (subWS t xs) ~ₜ toUcwf t `[ toHom xs ]
toUcwfDistSub (var _ ())      []
toUcwfDistSub (var _ zero)    (x ∷ xs) = q[<a,t>] (toUcwf x) (toHom xs)
toUcwfDistSub (var _ (suc i)) (x ∷ xs) = sym~ₜ $
  begin
    (toUcwf (var _ i) `[ p _ ]) `[ < toHom xs , toUcwf x > ]
  ≈⟨ sym~ₜ (∘sub (toUcwf (var _ i)) (p _) < toHom xs , toUcwf x >) ⟩
    toUcwf (var _ i) `[ p _ ∘ < toHom xs , toUcwf x > ]
  ≈⟨ sym~ₜ $
       congh~ₜ (_`[_] (toUcwf $ var _ i))
        (p∘<a,t> (toUcwf x) (toHom xs))
   ⟩
    toUcwf (var _ i) `[ toHom xs ]
  ≈⟨ sym~ₜ $ toUcwfDistSub (var _ i) xs ⟩ 
    (toUcwf $ subWS (var _ i) xs)
  ∎ where open EqR (UcwfTmS {_})
toUcwfDistSub (lam n t) xs = {!!}
toUcwfDistSub (app n t u) xs =
  begin
    app _ (toUcwf (subWS t xs)) (toUcwf (subWS u xs))
  ≈⟨ cong~ₜ (λ z → app _ z (toUcwf (subWS u xs))) (toUcwfDistSub t xs) ⟩
    app _ (toUcwf t `[ toHom xs ]) (toUcwf (subWS u xs))
  ≈⟨ cong~ₜ (app _ (toUcwf t `[ toHom xs ])) (toUcwfDistSub u xs) ⟩
    app _ (toUcwf t `[ toHom xs ]) (toUcwf u `[ toHom xs ])
  ≈⟨ {!!} ⟩
    app n (toUcwf t) (toUcwf u) `[ toHom xs ]
  ∎ where open EqR (UcwfTmS {_})

toHomDist∘ : ∀ {m n k} (xs : Vec (WellScopedTm n) k) (ys : Vec (WellScopedTm m) n)
               → toHom (compWS xs ys) ~ₕ (toHom xs) ∘ (toHom ys)
toHomDist∘ []       ys = sym~ₕ (∘<> (toHom ys))
toHomDist∘ (x ∷ xs) ys = sym~ₕ $
  begin
    < toHom xs , toUcwf x > ∘ toHom ys
  ≈⟨ <a,t>∘s (toUcwf x) (toHom xs) (toHom ys) ⟩
    < toHom xs ∘ toHom ys , toUcwf x `[ toHom ys ] >
  ≈⟨ cong~ₕ (λ z → < z , _ >) (sym~ₕ $ toHomDist∘ xs ys) ⟩
    < toHom (compWS xs ys) , toUcwf x `[ toHom ys ] >
  ≈⟨ congt~ₕ (λ z → < _ , z >) (sym~ₜ $ toUcwfDistSub x ys) ⟩
    < toHom (compWS xs ys) , toUcwf (subWS x ys) >
  ∎ where open EqR (HomCwfS {_} {_})

ucwf∘ws (q n)       = refl~ₜ
ucwf∘ws (u `[ ts ]) = sym~ₜ $
  begin
     toUcwf (subWS (toWs u) (toVec ts))
  ≈⟨ toUcwfDistSub (toWs u) (toVec ts) ⟩
    toUcwf (toWs u) `[ toHom (toVec ts) ]
  ≈⟨ sym~ₜ $ cong~ₜ (λ z → z `[ _ ]) (ucwf∘ws u) ⟩
    u `[ toHom (toVec ts) ]
  ≈⟨ sym~ₜ (congh~ₜ (λ z → _ `[ z ]) (hom∘vec ts)) ⟩
    u `[ ts ]
  ∎ where open EqR (UcwfTmS {_}) 
ucwf∘ws (lam n t)   = cong~ₜ (lam n) (ucwf∘ws t)
ucwf∘ws (app n t u) = trans~ₜ (cong~ₜ (app n t) (ucwf∘ws u))
                        (cong~ₜ (λ z → app n z (toUcwf $ toWs u)) (ucwf∘ws t))

hom∘vec (id zero)    = id₀
hom∘vec (id (suc m)) =
  begin
    id (suc m)
  ≈⟨ id<p,q> ⟩
    < p _ , q _ >
  ≈⟨ cong~ₕ <_, q _ > (hom∘vec (p m)) ⟩
    < toHom (projSub m) , q _ >
  ≈⟨ help m ⟩
    < toHom $ tail (idSub _) , q _ >
  ∎ where open EqR (HomCwfS {_} {_})
          help : ∀ m → < toHom (projSub m) , q m >
                         ~ₕ < toHom (tail $ idSub _) , q m >
          help m rewrite tailIdp m = refl~ₕ
hom∘vec (ts ∘ us) = sym~ₕ $
  begin
    toHom (compWS (toVec ts) (toVec us))
  ≈⟨ toHomDist∘ (toVec ts) (toVec us) ⟩
    toHom (toVec ts) ∘ toHom (toVec us)
  ≈⟨ cong~ₕ (λ z → z ∘ _) (sym~ₕ $ hom∘vec ts) ⟩
    ts ∘ toHom (toVec us)
  ≈⟨ cong~ₕ (λ z → _ ∘ z) (sym~ₕ $ hom∘vec us) ⟩
    ts ∘ us
  ∎ where open EqR (HomCwfS {_} {_})
hom∘vec (p zero) = hom0~<> $ p zero
hom∘vec (p (suc n)) =
  begin
    p (1 + n)
  ≈⟨ sym~ₕ (∘lid (p (suc n))) ⟩
    id (1 + n) ∘ p (1 + n)
  ≈⟨ cong~ₕ (_∘ p (suc n)) id<p,q> ⟩
    < p n , q n > ∘ p (1 + n)
  ≈⟨ <a,t>∘s (q n) (p n) (p (suc n)) ⟩
    < p n ∘ p (1 + n) , q n `[ p (1 + n) ] >
  ≈⟨ cong~ₕ (λ x → < x ∘ p (1 + n) , q n `[ p (1 + n) ] >) (hom∘vec (p n)) ⟩ 
    < toHom (projSub n) ∘ p (1 + n) , q n `[ p (1 + n) ] >
  ≈⟨ {!!} ⟩ 
    < toHom (tail $ projSub (1 + n)) , q n `[ p (1 + n) ] >
  ∎ where open EqR (HomCwfS {_} {_})
hom∘vec <> = refl~ₕ
hom∘vec < u , x > = sym~ₕ $
  begin
    < toHom (toVec u) , toUcwf (toWs x) >
  ≈⟨ sym~ₕ $ cong~ₕ (<_, toUcwf (toWs x) >) (hom∘vec u) ⟩
    < u , toUcwf (toWs x) >
  ≈⟨ sym~ₕ $ congt~ₕ (< u ,_>) (ucwf∘ws x) ⟩
    < u , x >
  ∎ where open EqR (HomCwfS {_} {_})

ws∘ucwf (var _ zero)    = refl
ws∘ucwf (var _ (suc x)) = sym $
  begin
    subWS (toWs $ toUcwf (var _ x)) (projSub _)
  ≡⟨ sym $ cong (flip subWS (projSub _)) (ws∘ucwf (var _ x)) ⟩
    subWS (var _ x) (projSub _)
  ≡⟨⟩
    lookup x (projSub _)
  ≡⟨ lookupPLemma _ x ⟩
    var (suc _) (suc x)
  ∎ where open ≡-Reasoning
ws∘ucwf (lam n t)   = cong (lam n) (ws∘ucwf t)
ws∘ucwf (app n t u) = trans (cong (app n t) (ws∘ucwf u))
                        (cong (λ z → app n z (toWs $ toUcwf u)) (ws∘ucwf t))

vec∘hom [] = refl
vec∘hom (x ∷ xs)
  rewrite sym (vec∘hom xs) |
          sym (ws∘ucwf x) = refl
