module Unityped.TermModels where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_] ; tabulate ; head ; tail)
open import Data.Vec.Properties using (lookup∘tabulate ; lookup-allFin)
open import Data.Fin using (Fin ; zero ; suc ; raise ; _+_ ; fromℕ)
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

toWs (q n)      = qWS n
toWs (t `[ h ]) = subWS (toWs t) (toVec h)

toUcwf (var _ zero)    = q _
toUcwf (var _ (suc i)) = weaken (toUcwf (var _ i))

-- Inverses
wellscoped∘ucwf : ∀ {n}   (t : WellScopedTm n) → t ≡ toWs (toUcwf t)
ucwf∘wellscoped : ∀ {n}   (u : UcwfTm n) → u ~ₜ toUcwf (toWs u)
vec∘hom         : ∀ {m n} (v : Vec (WellScopedTm m) n) → v ≡ toVec (toHom v)
hom∘vec         : ∀ {n m} (u : HomCwf m n) → u ~ₕ toHom (toVec u)

wellscoped∘ucwf (var _ zero)    = refl
wellscoped∘ucwf (var _ (suc x)) = sym $
  begin
    subWS (toWs $ toUcwf (var _ x)) (projSub _)
  ≡⟨ sym $ cong (flip subWS (projSub _)) (wellscoped∘ucwf (var _ x)) ⟩
    subWS (var _ x) (projSub _)
  ≡⟨⟩
    lookup x (projSub _)
  ≡⟨ lookupPLemma _ x ⟩
    var (suc _) (suc x)
  ∎ where open ≡-Reasoning

vec∘hom [] = refl
vec∘hom (x ∷ xs)
  rewrite sym (vec∘hom xs) |
          sym (wellscoped∘ucwf x) = refl

lemma2q : ∀ {n} (u : UcwfTm (suc n)) → toWs u ≡ qWS _ → (toUcwf (toWs u)) ~ₜ q _
lemma2q u pr rewrite pr = refl~ₜ

lemma2Wk : ∀ {n x} (u : UcwfTm (suc n)) → toWs u ≡ var (suc n) (suc x)
                   → toUcwf (toWs u) ~ₜ (toUcwf $ var (suc n) (suc x))
lemma2Wk u pr rewrite pr = refl~ₜ

empty~m : ∀ {n} (h : HomCwf n 0) → toVec h ≡ [] → toHom (toVec h) ~ₕ <>
empty~m h pr rewrite pr = refl~ₕ

ext~<,> : ∀ {m n x xs} (h : HomCwf m (suc n)) → toVec h ≡ x ∷ xs
            → toHom (toVec h) ~ₕ < toHom xs , toUcwf x >
ext~<,> _ pr rewrite pr = refl~ₕ   

ucwf∘wellscoped (q n) = refl~ₜ
ucwf∘wellscoped (u `[ id _ ]) rewrite t[id]=t (toWs u)
  = trans~ₜ (sym~ₜ (subId u)) (ucwf∘wellscoped u)
  
ucwf∘wellscoped (u `[ ts ∘ us ]) with toVec ts | inspect toVec ts
                                    | toWs u   | inspect toWs u
ucwf∘wellscoped (u `[ ts ∘ us ]) | []     | _         | var .0 ()  | _
ucwf∘wellscoped (u `[ ts ∘ us ]) | x ∷ xs | [ =x∷xs ] | var _ zero | [ =var ] =
  begin
    u `[ ts ∘ us ]
  ≈⟨ cong~ₜ (_`[ ts ∘ us ]) (ucwf∘wellscoped u) ⟩
    (toUcwf (toWs u)) `[ ts ∘ us ]
  ≈⟨ cong~ₜ (_`[ ts ∘ us ]) (lemma2q u =var) ⟩
    q _ `[ ts ∘ us ]
  ≈⟨ congh~ₜ (λ r → q _ `[ r ∘ us ]) {!!} ⟩ --(hom∘vec ts) bruuuh .. δεν ειναι σωστή αναδρομή εδω; έλεος..
    q _ `[ toHom (toVec ts) ∘ us ]
  ≈⟨ congh~ₜ (λ r → q _ `[ r ∘ us ]) (ext~<,> ts =x∷xs) ⟩
    q _ `[ < toHom xs , toUcwf x > ∘ us ]
  ≈⟨ congh~ₜ (_`[_] (q _)) (<a,t>∘s (toUcwf x) (toHom xs) us) ⟩ 
    q _ `[ < toHom xs ∘ us , (toUcwf x) `[ us ] > ]
  ≈⟨ sym~ₜ (q[<a,t>] (toUcwf x `[ us ]) (toHom xs ∘ us)) ⟩
   toUcwf x `[ us ]
  ≈⟨ {!!} ⟩ -- recursive call fails termination check
   toUcwf (subWS (toWs (toUcwf x)) (toVec us))
  ≈⟨ help ⟩
   toUcwf (subWS x (toVec us))
  ∎ where open EqR (UcwfTmS {_})
          help : toUcwf (subWS (toWs (toUcwf x)) (toVec us)) ~ₜ (toUcwf (subWS x (toVec us)))
          help rewrite sym $ wellscoped∘ucwf x = refl~ₜ
{-
  u`[ts ∘ us]
~ q`[ts ∘ us]
~ q`[toHom (toVec ts) ∘ us]
~ q`[< toHom xs ∘ us , (toUcwf x)`[us] >]
~ (toUcwf x)`[us]
-}
ucwf∘wellscoped (u `[ ts ∘ us ]) | x ∷ xs | [ =x∷xs ] | var _ (suc i) | [ =var ] = {!!}
  where open Reveal_·_is_
        --open EqR (UcwfTmS {_})

ucwf∘wellscoped (u `[ p _ ]) with toWs u
                                | inspect toWs u
ucwf∘wellscoped (u `[ p _ ]) | var _ x
                             | [ var=u ] = sym~ₜ $
  begin
    toUcwf (subWS (var _ x) (projSub _))
  ≈⟨ help ⟩
    weaken (toUcwf $ toWs u)
  ≈⟨ sym~ₜ $ cong~ₜ weaken (ucwf∘wellscoped u) ⟩
    u `[ p _ ]
  ∎ where open EqR (UcwfTmS {_})
          open Reveal_·_is_
          help : toUcwf (subWS (var _ x) (projSub _)) ~ₜ weaken (toUcwf $ toWs u)
          help rewrite subPLift (var _ x)
                              | liftVar _ x
                              | var=u = refl~ₜ                         
ucwf∘wellscoped (u `[ <> ]) with toWs u
ucwf∘wellscoped (u `[ <> ]) | var .0 ()
ucwf∘wellscoped (u `[ < xs , x > ]) with toWs u
                                       | inspect toWs u
ucwf∘wellscoped (u `[ < xs , x′ > ]) | var _ zero
                                     | [ q=2WSu ] =
  begin
     u `[ < xs , x′ > ]
   ≈⟨ cong~ₜ _`[ < xs , x′ > ] (ucwf∘wellscoped u) ⟩
     (toUcwf (toWs u)) `[ < xs , x′ > ]
   ≈⟨ cong~ₜ _`[ < xs , x′ > ] (lemma2q u q=2WSu) ⟩
     (q _) `[ < xs , x′ > ]
   ≈⟨ sym~ₜ (q[<a,t>] x′ xs) ⟩
     x′
   ≈⟨ ucwf∘wellscoped x′ ⟩
     toUcwf (toWs x′)
   ∎ where open EqR (UcwfTmS {_})
           open Reveal_·_is_         
ucwf∘wellscoped (u `[ < xs , x′ > ]) | var _ (suc x)
                                     | [ var=u ] =
  begin
    u `[ < xs , x′ > ]
  ≈⟨ cong~ₜ _`[ < xs , x′ > ] (ucwf∘wellscoped u) ⟩
    (toUcwf $ toWs u) `[ < xs , x′ > ]
  ≈⟨ cong~ₜ _`[ < xs , x′ > ] (lemma2Wk u var=u) ⟩
    ((toUcwf $ var _ x) `[ p _ ]) `[ < xs , x′ > ]
  ≈⟨ sym~ₜ $ ∘sub (toUcwf (var _ x)) (p _) < xs , x′ > ⟩
    (toUcwf $ var _ x) `[ (p _) ∘ < xs , x′ > ]
  ≈⟨ sym~ₜ (congh~ₜ ((toUcwf (var _ x)) `[_]) (p∘<a,t> x′ xs)) ⟩
    (toUcwf $ var _ x) `[ xs ]
  ≈⟨ {!!} ⟩ -- recursive call causes termination checker issue, but should be structurally recursive (bruuh)
    toUcwf (subWS (toWs (toUcwf $ var _ x)) (toVec xs))
  ≈⟨ help₂ xs x ⟩
    toUcwf (subWS (var _ x) (toVec xs))
  ∎ where open Reveal_·_is_
          open EqR (UcwfTmS {_})
          help₂ : ∀ {n m} (xs : HomCwf m n) (x : Fin n) →
            toUcwf (subWS (toWs (toUcwf $ var n x)) (toVec xs))
             ~ₜ toUcwf (subWS (var n x) (toVec xs))
          help₂ {n} {_} _ x rewrite sym $ wellscoped∘ucwf (var n x) = refl~ₜ

hom∘vec (id zero)    = id₀ {0} {0}
hom∘vec (id (suc m)) = 
  begin
    id (suc m)
  ≈⟨ id<p,q> ⟩
    < p _ , q _ >
  ≈⟨ cong~ₕ <_, q _ > (hom∘vec $ p m) ⟩
    < toHom (projSub m) , q _ >
  ≈⟨ help m ⟩
    < toHom $ tail (idSub _) , q _ >
  ∎ where open EqR (HomCwfS {suc m} {suc m})
          help : ∀ m → < toHom (projSub m) , q m >
                         ~ₕ < toHom (tail $ idSub _) , q m >
          help m rewrite tailIdp m = refl~ₕ
hom∘vec (hnk ∘ hmn) with toVec hnk | inspect toVec hnk
hom∘vec (hnk ∘ hmn) | [] | [ =[] ] =
  begin
    hnk ∘ hmn
  ≈⟨ cong~ₕ (flip _∘_ $ hmn) (hom∘vec hnk) ⟩
    (toHom (toVec hnk)) ∘ hmn
  ≈⟨ cong~ₕ (flip _∘_ $ hmn) (empty~m hnk =[]) ⟩
    <> ∘ hmn
  ≈⟨ ∘<> hmn ⟩
    <>
  ∎ where open EqR (HomCwfS {_} {_})
hom∘vec (hnk ∘ hmn) | x ∷ xs | [ =x∷xs ] = sym~ₕ $
  begin
    toHom (subWS x (toVec hmn) ∷ compWS xs (toVec hmn))
  ≈⟨ help x xs hmn ⟩
    toHom (subWS (toWs (toUcwf x)) (toVec hmn)
                ∷ compWS (toVec (toHom xs)) (toVec hmn))
  ≈⟨ sym~ₕ $ cong~ₕ (λ z → < z , _ >) (hom∘vec $ (toHom xs) ∘ hmn) ⟩
    < (toHom xs) ∘ hmn , toUcwf (subWS (toWs (toUcwf x)) (toVec hmn)) >
  ≈⟨ sym~ₕ $ congt~ₕ (λ z → < _ , z >) (ucwf∘wellscoped $ (toUcwf x) `[ hmn ]) ⟩
    < (toHom xs) ∘ hmn , (toUcwf x) `[ hmn ] >
  ≈⟨ sym~ₕ (<a,t>∘s (toUcwf x) (toHom xs) hmn) ⟩
    < toHom xs , toUcwf x > ∘ hmn
  ≈⟨ sym~ₕ (cong~ₕ (flip _∘_ $ hmn) (ext~<,> hnk =x∷xs)) ⟩
    toHom (toVec hnk) ∘ hmn
  ≈⟨ sym~ₕ (cong~ₕ (flip _∘_ $ hmn) (hom∘vec hnk)) ⟩
    hnk ∘ hmn
  ∎
  where open Reveal_·_is_
        open EqR (HomCwfS {_} {_})
        help : ∀ {n m : Nat} (x : WellScopedTm _) (xs : Vec (WellScopedTm _) n)
                             (hmn : HomCwf m _)
                 → toHom (subWS x (toVec hmn) ∷ compWS xs (toVec hmn))
                    ~ₕ toHom (subWS (toWs (toUcwf x)) (toVec hmn)
                               ∷ compWS (toVec (toHom xs)) (toVec hmn))
        help {n = n₁} x xs hmn rewrite sym $ wellscoped∘ucwf x
                                     | sym $ vec∘hom xs = refl~ₕ
hom∘vec (p n) = {!!}
hom∘vec (<>) = refl~ₕ
hom∘vec < u , x > = sym~ₕ $
  begin
    < toHom (toVec u) , toUcwf (toWs x) >
  ≈⟨ sym~ₕ $ cong~ₕ (<_, toUcwf (toWs x) >) (hom∘vec u) ⟩
    < u , toUcwf (toWs x) >
  ≈⟨ sym~ₕ $ congt~ₕ (< u ,_>) (ucwf∘wellscoped x) ⟩
    < u , x >
  ∎ where open EqR (HomCwfS {_} {_})
