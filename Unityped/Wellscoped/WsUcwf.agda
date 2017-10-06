{-# OPTIONS --allow-unsolved-metas #-}
module Unityped.Wellscoped.WsUcwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function renaming (_∘_ to _◯_) using (_$_ ; flip)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Unityped.Ucwf
open import Unityped.WSModel
open import Unityped.Wellscoped.Properties
open ≡-Reasoning

id=<p,q> : ∀ n → id (suc n) ≡ q n ∷ p n 
id=<p,q> n = cong (_∷_ (q _)) (tailIdp n)

t[id]=t : ∀ {n} → (t : WellScopedTm n) → t ′[ id n ] ≡ t
t[id]=t (var n i) = lookupInId n i
t[id]=t (lam n t) = trans (cong (lam _ ◯ t ′[_]) (sym $ id=<p,q> _))
                          (cong (lam n) (t[id]=t t))
t[id]=t (app n t u) = trans (cong (flip (app n) (u ′[ id n ])) (t[id]=t t))
                            (cong (app n t) (t[id]=t u))

id0=[] : id 0 ≡ empt
id0=[] = refl

∘-empty : ∀ {m n} (ts : Vec (WellScopedTm m) n) → empt ∘ ts ≡ empt
∘-empty _ = refl

∘-assoc : ∀ {m n k j} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n)
    (vs : Vec (WellScopedTm j) m) → (ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)

t[∘] : ∀ {m n k} (t : WellScopedTm n) (ts : Vec (WellScopedTm k) n)
    (us : Vec (WellScopedTm m) k) → t ′[ ts ∘ us ] ≡ t ′[ ts ] ′[ us ]

p∘x∷ts : ∀ {n k} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k) → p k ∘ (t ∷ ts) ≡ ts
p∘x∷ts t ts = begin
  p  _  ∘ (t ∷ ts)                    ≡⟨ cong (_∘ (t ∷ ts)) (p=p' _) ⟩
  p′ _  ∘ (t ∷ ts)                    ≡⟨ p∘-lookup (t ∷ ts) ⟩
  map (flip lookup (t ∷ ts)) (1toN _) ≡⟨ map-lookup-↑ (t ∷ ts) ⟩
  ts                                  ∎

tailComp : ∀ n → p n ∘ p (1 + n) ≡ tail (p (1 + n))
tailComp n = p∘x∷ts _ (tail (p _))

t[∘] (var _ zero)    (v ∷ ts) us = refl
t[∘] (var _ (suc i)) (v ∷ ts) us = t[∘] (var _ i) ts us
t[∘] (lam n t)       ts       us = sym $ begin
  lam _ (t ′[ q _ ∷ ↑ ts ] ′[ q _ ∷ ↑ us ])
    ≡⟨ cong (lam _) (sym $ t[∘] t (q _ ∷ ↑ ts) (q _ ∷ ↑ us)) ⟩
  lam _ (t ′[ q _ ∷ (↑ ts ∘ (q _ ∷ ↑ us)) ])
    ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ])) (sym $ liftDist ts us) ⟩
  lam _ (t ′[ q _ ∷ ↑ (ts ∘ us) ])
    ∎
t[∘] (app n t u) ts us =
  trans (cong (λ z → app _ z (u ′[ ts ∘ us ])) (t[∘] t ts us))
        (cong (app _ (t ′[ ts ] ′[ us ])) (t[∘] u ts us))

∘-assoc [] us vs = refl
∘-assoc (x ∷ ts) us vs = sym $ begin
  x ′[ us ∘ vs ] ∷ ts ∘ (us ∘ vs)    ≡⟨ cong (_∷ ts ∘ (us ∘ vs)) (t[∘] x us vs) ⟩
  x ′[ us ] ′[ vs ] ∷ ts ∘ (us ∘ vs) ≡⟨ sym (cong (_∷_ (x ′[ us ] ′[ vs ])) (∘-assoc ts us vs)) ⟩
  x ′[ us ] ′[ vs ] ∷ (ts ∘ us) ∘ vs ∎

∘-lid : ∀ {m n} (ts : Vec (WellScopedTm m) n) → id n ∘ ts ≡ ts
∘-lid [] = refl
∘-lid (x ∷ ts) =
  trans (cong (λ a → (q _ ′[ x ∷ ts ]) ∷ a ∘ (x ∷ ts)) (tailIdp _))
        (cong (λ a → (q _ ′[ x ∷ ts ]) ∷ a) (p∘x∷ts x ts))

∘-rid : ∀ {m n} (ts : Vec (WellScopedTm m) n) → ts ∘ id m  ≡ ts
∘-rid [] = refl
∘-rid (x ∷ ts) rewrite t[id]=t x
                     | ∘-rid ts = refl

wsIsUcwf : Ucwf (WellScopedTm)
wsIsUcwf = record
             { id    = id
             ; <>    = empt
             ; p     = p
             ; q     = q
             ; _∘_   = _∘_
             ; _[_]  = _′[_]
             ; <_,_> = ext
             ; id₀   = id0=[]
             ; ∘<>   = ∘-empty
             ; varp  = id=<p,q> _ 
             ; idL   = ∘-lid
             ; idR   = ∘-rid
             ; assoc = ∘-assoc
             ; varId = t[id]=t
             ; pCons = p∘x∷ts
             ; qCons = λ _ _ → refl
             ; clos  = t[∘]
             ; maps  = λ _ _ _ → refl
             } 
