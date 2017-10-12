module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Nat.Properties
open import Relation.Binary using (IsEquivalence ; Setoid)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P

data CwfTm : Nat → Set
data Hom : Nat → Nat → Set

data CwfTm where
  q    : (n : Nat) → CwfTm (suc n)
  _[_] : {m n : Nat} → CwfTm n → Hom m n → CwfTm m
  lam  : (n : Nat) → CwfTm (suc n) → CwfTm n
  app  : (n : Nat) → CwfTm n → CwfTm n → CwfTm n

data Hom where
  id    : (m : Nat) → Hom m m
  _⋆_   : {m n k : Nat} → Hom n k → Hom m n → Hom m k
  p     : (n : Nat) → Hom (suc n) n
  <>    : {m : Nat} → Hom m zero
  <_,_> : {m n : Nat} → Hom m n → CwfTm m → Hom m (suc n)

weaken : ∀ {n} → CwfTm n → CwfTm (suc n)
weaken t = t [ p _ ]

infix 10 _~ₜ_
infix 10 _~ₕ_

data _~ₜ_ : ∀ {n} → CwfTm n → CwfTm n → Set
data _~ₕ_ : ∀ {n m} → Hom n m → Hom n m → Set

data _~ₜ_  where
  subId    : ∀ {n} (u : CwfTm n) → u ~ₜ u [ (id n) ]
  q[<a,t>] : ∀ {m n} (t : CwfTm n) (ts : Hom n m) → t ~ₜ (q m) [ < ts , t > ]
  ⋆sub     : ∀ {m n k} (t : CwfTm n) (ts : Hom k n) (us : Hom m k)
               →  t [ ts ⋆ us ] ~ₜ  (t [ ts ])[ us ]
  β        : ∀ {n} (t : CwfTm (suc n)) (u : CwfTm n)
               → app n (lam n t) u ~ₜ t [ < id n , u > ]
  η        : ∀ {n} (t : CwfTm n) → lam n (app (suc n) (t [ p n ]) (q n)) ~ₜ t
  appCm    : ∀ {n m} (t : CwfTm n) (u : CwfTm n) (ts : Hom m n) → app m (t [ ts ]) (u [ ts ]) ~ₜ app n t u [ ts ]
  lamCm    : ∀ {n m} (t : CwfTm (suc n)) (ts : Hom m n) → lam n t [ ts ] ~ₜ lam m (t [ < ts ⋆ p m , q m > ])
  sym~ₜ    : ∀ {n} {u u′ : CwfTm n} → u ~ₜ u′ → u′ ~ₜ u
  trans~ₜ  : ∀ {m} {t u v : CwfTm m} → t ~ₜ u → u ~ₜ v → t ~ₜ v
  cong~ₜ   : ∀ {m n} (f : CwfTm m → CwfTm n) {h u : CwfTm m} → h ~ₜ u → f h ~ₜ f u
  congh~ₜ  : ∀ {m n k} (f : Hom m n → CwfTm k) {h v : Hom m n} → h ~ₕ v → f h ~ₜ f v

refl~ₜ : ∀ {n} {u : CwfTm n} → u ~ₜ u
refl~ₜ = trans~ₜ (subId _) (sym~ₜ (subId _))

data _~ₕ_ where
  id₀     : id 0 ~ₕ <>
  ⋆<>     : ∀ {m n} (ts : Hom m n) → (<> ⋆ ts) ~ₕ <>
  id<p,q> : ∀ {n} → id (suc n) ~ₕ < p n , q n >
  ⋆lid    : ∀ {m n} (ts : Hom m n) → (id n) ⋆ ts ~ₕ ts
  ⋆rid    : ∀ {m n} (ts : Hom m n) → ts ⋆ (id m) ~ₕ ts
  ⋆asso   : ∀ {m n k p} (ts : Hom n k) (us : Hom m n) (vs : Hom p m)
              → (ts ⋆ us) ⋆ vs  ~ₕ ts ⋆ (us ⋆ vs)
  p⋆<a,t> : ∀ {m n} (u : CwfTm m) (us : Hom m n)
              → us ~ₕ (p  n) ⋆ < us , u >
  <a,t>⋆s : ∀ {m n k} (t : CwfTm n) (ts : Hom n k) (us : Hom m n)
              → < ts , t > ⋆ us  ~ₕ < ts ⋆ us , t [ us ] > 
  sym~ₕ   : ∀ {m n} {h : Hom m n} {t : Hom m n} → h ~ₕ t → t ~ₕ h
  trans~ₕ : ∀ {m n} {h t v : Hom m n} → h ~ₕ t → t ~ₕ v → h ~ₕ v
  cong~ₕ  : ∀ {m n k p} (f : Hom m n → Hom k p) {h u : Hom m n} → h ~ₕ u → f h ~ₕ f u
  congt~ₕ : ∀ {m n} (f : CwfTm m → Hom m n) {t u : CwfTm m} → t ~ₜ u → f t ~ₕ f u

hom0~<> : ∀ {n} (ts : Hom n 0) → ts ~ₕ <>

eta : ∀ {n m} (ts : Hom m (1 + n)) → ts ~ₕ < p n ⋆ ts , q n [ ts ] >

refl~ₕ : ∀ {n m} {h : Hom m n} → h ~ₕ h
refl~ₕ = trans~ₕ (sym~ₕ (⋆lid _)) (⋆lid _)

~ₜequiv : ∀ {n} → IsEquivalence (_~ₜ_ {n})
~ₜequiv = record { refl  = refl~ₜ
                 ; sym   = sym~ₜ
                 ; trans = trans~ₜ }

CwfTmS : ∀ {n} → Setoid _ _
CwfTmS {n} =
  record { Carrier = CwfTm n
         ; _≈_ = _~ₜ_
         ; isEquivalence = ~ₜequiv }

~ₕequiv : ∀ {n m} → IsEquivalence (_~ₕ_ {n} {m})
~ₕequiv = record { refl  = refl~ₕ
                 ; sym   = sym~ₕ
                 ; trans = trans~ₕ }
                 
HomS : ∀ {n m} → Setoid _ _
HomS {n} {m} =
  record { Carrier = Hom m n
         ; _≈_ = _~ₕ_
         ; isEquivalence = ~ₕequiv }

hom0~<> ts = begin
  ts        ≈⟨ sym~ₕ (⋆lid ts) ⟩
  id 0 ⋆ ts ≈⟨ cong~ₕ (_⋆ ts) id₀ ⟩
  <> ⋆ ts   ≈⟨ ⋆<> ts ⟩ 
  <>        ∎
  where open EqR (HomS {0} {_})

eta ts = begin
  ts                        ≈⟨ sym~ₕ (⋆lid ts) ⟩
  id _ ⋆ ts                 ≈⟨ cong~ₕ (λ z → z ⋆ ts) id<p,q> ⟩
  < p _ , q _ > ⋆ ts        ≈⟨ <a,t>⋆s (q _) (p _) ts ⟩
  < p _ ⋆ ts , q _ [ ts ] > ∎
  where open EqR (HomS {_} {_})
