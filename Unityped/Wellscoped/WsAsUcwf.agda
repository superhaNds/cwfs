module Unityped.Wellscoped.WsAsUcwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_$_)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Unityped.Ucwf
open import Unityped.WSModel
open import Unityped.Wellscoped.Properties
open ≡-Reasoning

id=<p,q> : ∀ (n : Nat) → id (suc n) ≡ q n ∷ p n 
id=<p,q> n = cong (_∷_ (q _)) (tailIdp n)

t[id]=t : ∀ {n} → (t : WellScopedTm n) → t ′[ id n ] ≡ t
t[id]=t (var n i) = lookupIdLemma n i
t[id]=t (lam n t) = trans (cong (λ x → lam _ (t ′[ x ])) (sym $ id=<p,q> _))
                          (cong (lam n) (t[id]=t t))
t[id]=t (app n t u) = trans (cong (λ z → app n z (u ′[ id n ])) (t[id]=t t))
                            (cong (app n t) (t[id]=t u))

id0=[] : id 0 ≡ empt
id0=[] = refl

∘-empty : ∀ {m n} (ts : Vec (WellScopedTm m) n) → empt ∘ ts ≡ empt
∘-empty _ = refl

∘-assoc : ∀ {m n k j} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n)
    (vs : Vec (WellScopedTm j) m) → (ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)

compInSub : ∀ {m n k} (t : WellScopedTm n) (ts : Vec (WellScopedTm k) n)
    (us : Vec (WellScopedTm m) k) → t ′[ ts ∘ us ] ≡ t ′[ ts ] ′[ us ]

postulate
  pxts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k) → p k ∘ (t ∷ ts) ≡ ts
  ∘as : ∀ {m n k j} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n)
            (vs : Vec (WellScopedTm j) m) → (ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)

p∘x∷ts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k) → p k ∘ (t ∷ ts) ≡ ts
p∘x∷ts {n} {zero} t [] = refl
p∘x∷ts {n} {suc k} t (x ∷ ts) = pxts t (x ∷ ts)

tailComp : ∀ n → (p n) ∘ (p (1 + n)) ≡ tail (p (1 + n))
tailComp n = p∘x∷ts _ (tail (p (suc n)))

compInSub (var _ zero)    (v ∷ ts) us = refl
compInSub (var _ (suc i)) (v ∷ ts) us = compInSub (var _ i) ts us
compInSub (lam n t)       ts       us = sym $
  begin
    _  ≡⟨ cong (lam _) (sym $ compInSub t (q _ ∷ map lift ts) (q _ ∷ map lift us)) ⟩
    _  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ∘ _ ])) (lift∘p ts) ⟩
    _  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ _ ∘ (q _ ∷ x) ])) (lift∘p us) ⟩
    _  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ])) (∘as ts (p _) (q _ ∷ (us ∘ p _))) ⟩ -- ∘-assoc ts (p _) (q _ ∷ comp us (p _))
    _  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ ts ∘ x ])) (p∘x∷ts (q _) (us ∘ p _)) ⟩  
    _  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ])) (sym (∘as ts us (p _))) ⟩ -- ∘-assoc ts us (p _)
    _  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ])) (sym (lift∘p (ts ∘ us))) ⟩ 
    _  ∎
compInSub (app n t u) ts us =
  trans (cong (λ z → app _ z (u ′[ ts ∘ us ])) (compInSub t ts us))
        (cong (app _ (t ′[ ts ] ′[ us ])) (compInSub u ts us))

∘-lid : ∀ {m n : Nat} (ts : Vec (WellScopedTm m) n) → id n ∘ ts ≡ ts
∘-lid [] = refl
∘-lid (x ∷ ts) =
  trans (cong (λ a → (q _ ′[ x ∷ ts ]) ∷ a ∘ (x ∷ ts)) (tailIdp _))
        (cong (λ a → (q _ ′[ x ∷ ts ]) ∷ a) (p∘x∷ts x ts))

∘-rid : ∀ {m n : Nat} (ts : Vec (WellScopedTm m) n) → ts ∘ id m  ≡ ts
∘-rid [] = refl
∘-rid (x ∷ ts) rewrite t[id]=t x
                     | ∘-rid ts = refl

∘-assoc []       us vs = refl
∘-assoc (x ∷ ts) us vs = sym $
  trans (cong (λ d → d ∷ ts ∘ (us ∘ vs)) (compInSub x us vs))
        (sym (cong (_∷_ (x ′[ us ] ′[ vs ])) (∘-assoc ts us vs)))

wsIsUcwf : Ucwf (WellScopedTm)
wsIsUcwf = record
             { id       = id
             ; <>       = empt
             ; p        = p
             ; q        = q
             ; _∘_      = _∘_
             ; _[_]     = _′[_]
             ; <_,_>    = ext
             ; id₀      = id0=[]
             ; ∘<>      = ∘-empty
             ; id<p,q>  = id=<p,q> _
             ; ∘lid     = ∘-lid
             ; ∘rid     = ∘-rid
             ; ∘asso    = ∘-assoc
             ; subid    = t[id]=t
             ; p∘<γ,α>  = p∘x∷ts
             ; q[<γ,α>] = λ _ _ → refl
             ; ∘inSub   = compInSub
             ; <δ,α>∘γ  = λ _ _ _ → refl
             }
