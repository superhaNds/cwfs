module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Relation.Binary using (IsEquivalence ; Setoid)
import Relation.Binary.EqReasoning as EqR

data UcwfTm : Nat → Set
data HomCwf : Nat → Nat → Set

data UcwfTm where
  q    : (n : Nat) → UcwfTm (suc n)
  _[_] : {m n : Nat} → UcwfTm n → HomCwf m n → UcwfTm m
  lam  : (n : Nat) → UcwfTm (suc n) → UcwfTm n
  app  : (n : Nat) → UcwfTm n → UcwfTm n → UcwfTm n

data HomCwf where
  id    : (m : Nat) → HomCwf m m
  _∘_   : {m n k : Nat} → HomCwf n k → HomCwf m n → HomCwf m k
  p     : (n : Nat) → HomCwf (suc n) n
  <>    : {m : Nat} → HomCwf m zero
  <_,_> : {m n : Nat} → HomCwf m n → UcwfTm m → HomCwf m (suc n)

weaken : ∀ {n} → UcwfTm n → UcwfTm (suc n)
weaken t = t [ p _ ]

infix 10 _~ₜ_
infix 10 _~ₕ_

data _~ₜ_ : ∀ {n m} → UcwfTm n → UcwfTm m → Set
data _~ₕ_ : ∀ {n m} → HomCwf n m → HomCwf n m → Set

data _~ₜ_  where
 subId    : ∀ {n} (u : UcwfTm n) → u ~ₜ u [ (id n) ]
 q[<a,t>] : ∀ {m n} (t : UcwfTm n) (ts : HomCwf n m) → t ~ₜ (q m) [ < ts , t > ]
 ∘sub     : ∀ {m n k} (t : UcwfTm n) (ts : HomCwf k n) (us : HomCwf m k)
              →  t [ ts ∘ us ] ~ₜ  (t [ ts ])[ us ]
 β        : ∀ {n} (t : UcwfTm (suc n)) (u : UcwfTm n)
              → app n (lam n t) u ~ₜ t [ < id n , u > ]
 sym~ₜ    : ∀ {n} {u u′ : UcwfTm n} → u ~ₜ u′ → u′ ~ₜ u
 trans~ₜ  : ∀ {m} {t u v : UcwfTm m} → t ~ₜ u → u ~ₜ v → t ~ₜ v
 cong~ₜ   : ∀ {m n} (f : UcwfTm m → UcwfTm n) {h u : UcwfTm m} → h ~ₜ u → f h ~ₜ f u
 congh~ₜ  : ∀ {m n} (f : HomCwf m n → UcwfTm m) {h v : HomCwf m n} → h ~ₕ v → f h ~ₜ f v

refl~ₜ : ∀ {n} {u : UcwfTm n} → u ~ₜ u
refl~ₜ = trans~ₜ (subId _) (sym~ₜ (subId _))

data _~ₕ_ where
  id₀     : id 0 ~ₕ <>
  ∘<>     : ∀ {m n} (ts : HomCwf m n) → (<> ∘ ts) ~ₕ <>
  id<p,q> : ∀ {n} → id (suc n) ~ₕ < p n , q n >
  ∘lid    : ∀ {m n} (ts : HomCwf m n) → (id n) ∘ ts ~ₕ ts
  ∘rid    : ∀ {m n} (ts : HomCwf m n) → ts ∘ (id m) ~ₕ ts
  ∘asso   : ∀ {m n k p} (ts : HomCwf n k) (us : HomCwf m n) (vs : HomCwf p m)
              → (ts ∘ us) ∘ vs  ~ₕ ts ∘ (us ∘ vs)
  p∘<a,t> : ∀ {m n} (u : UcwfTm m) (us : HomCwf m n)
              → us ~ₕ (p  n) ∘ < us , u >
  <a,t>∘s : ∀ {m n k} (t : UcwfTm n) (ts : HomCwf n k) (us : HomCwf m n)
              → < ts , t > ∘ us  ~ₕ < ts ∘ us , t [ us ] > 
  sym~ₕ   : ∀ {m n} {h : HomCwf m n} {t : HomCwf m n} → h ~ₕ t → t ~ₕ h
  trans~ₕ : ∀ {m n} {h t v : HomCwf m n} → h ~ₕ t → t ~ₕ v → h ~ₕ v
  cong~ₕ  : ∀ {m n k p} (f : HomCwf m n → HomCwf k p) {h u : HomCwf m n} → h ~ₕ u → f h ~ₕ f u
  congt~ₕ : ∀ {m n} (f : UcwfTm m → HomCwf m n) {t u : UcwfTm m} → t ~ₜ u → f t ~ₕ f u

hom0~<> : ∀ {n} (ts : HomCwf n 0) → ts ~ₕ <>

refl~ₕ : ∀ {n m} {h : HomCwf m n} → h ~ₕ h
refl~ₕ = trans~ₕ (sym~ₕ (∘lid _)) (∘lid _)

~ₜequiv : ∀ {n} → IsEquivalence (_~ₜ_ {n})
~ₜequiv = record { refl  = refl~ₜ
                 ; sym   = sym~ₜ
                 ; trans = trans~ₜ }

UcwfTmS : ∀ {n} → Setoid _ _
UcwfTmS {n} =
  record { Carrier = UcwfTm n
         ; _≈_ = _~ₜ_
         ; isEquivalence = ~ₜequiv }

~ₕequiv : ∀ {n m} → IsEquivalence (_~ₕ_ {n} {m})
~ₕequiv = record { refl  = refl~ₕ
                 ; sym   = sym~ₕ
                 ; trans = trans~ₕ }
                 
HomCwfS : ∀ {n m} → Setoid _ _
HomCwfS {n} {m} =
  record { Carrier = HomCwf m n
         ; _≈_ = _~ₕ_
         ; isEquivalence = ~ₕequiv }

hom0~<> ts =
  begin
    ts
  ≈⟨ sym~ₕ (∘lid ts) ⟩
    id 0 ∘ ts
  ≈⟨ cong~ₕ (_∘ ts) id₀ ⟩
    <> ∘ ts
  ≈⟨ ∘<> ts ⟩ 
    <>
  ∎ where open EqR (HomCwfS {0} {_})
