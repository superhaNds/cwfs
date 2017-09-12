module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Relation.Binary using (IsEquivalence ; Setoid)

data UcwfTm : Nat → Set
data HomCwf : Nat → Nat → Set

data UcwfTm where
  q   : (n : Nat) → UcwfTm (suc n)
  sub : (m n : Nat) → UcwfTm n → HomCwf m n → UcwfTm m

data HomCwf where
  id       : (m : Nat) → HomCwf m m
  comp     : (m n k : Nat) → HomCwf n k → HomCwf m n → HomCwf m k
  p        : (n : Nat) → HomCwf (suc n) n
  <>       : (m : Nat) → HomCwf m zero
  _,_<_,_> : (m n : Nat) → HomCwf m n → UcwfTm m → HomCwf m (suc n)

weaken : ∀ {n} → UcwfTm n → UcwfTm (suc n)
weaken t = sub (suc _) _ t (p _)

infix 10 _~ₜ_
infix 10 _~ₕ_

data _~ₜ_ : ∀ {n} (u₁ u₂ : UcwfTm n) → Set
data _~ₕ_ : ∀ {n m} (h₁ h₂ :  HomCwf n m) → Set

data _~ₜ_  where
 subId : ∀ {n} (u : UcwfTm n) → u ~ₜ sub n n u (id n)
 q[<a,t>] : ∀ {m n} (t : UcwfTm n) (ts : HomCwf n m)
              → t ~ₜ sub n (suc m) (q m) (n , m < ts , t >)
 ∘sub : ∀ {m n k} (t : UcwfTm n) (ts : HomCwf k n) (us : HomCwf m k)
          → sub m n t (comp m k n ts us)
           ~ₜ sub m k (sub k n t ts) us
 sym~ₜ : ∀ {n} {u u′ : UcwfTm n} → u ~ₜ u′ → u′ ~ₜ u
 trans~ₜ : ∀ {m} {t u v : UcwfTm m} → t ~ₜ u → u ~ₜ v → t ~ₜ v
 cong~ₜ  : ∀ {m n} (f : UcwfTm m → UcwfTm n) {h u : UcwfTm m} →
             h ~ₜ u → f h ~ₜ f u
 {- congh~ₜ : ∀ {m n} (f : HomCwf m n → UcwfTm m) {h v : HomCwf m n}
             → h ~ₕ v → f h ~ₜ f v -}

refl~ₜ : ∀ {n} {u : UcwfTm n} → u ~ₜ u
refl~ₜ = trans~ₜ (subId _) (sym~ₜ (subId _))

data _~ₕ_ where 
  id₀ : id zero ~ₕ <> zero
  ∘<> : ∀ {m n} (ts : HomCwf m n) → comp m n zero (<> n) ts ~ₕ <> m
  id<p,q> : ∀ {n} → id (suc n) ~ₕ suc n , n < p n , q n >
  ∘lid : ∀ {m n} (ts : HomCwf m n) → comp m n n (id n) ts ~ₕ ts
  ∘rid : ∀ {m n} (ts : HomCwf m n) → comp m m n ts (id m) ~ₕ ts
  ∘asso : ∀ {m n k p} (ts : HomCwf n k) (us : HomCwf m n) (vs : HomCwf p m) →
            comp p m k (comp m n k ts us) vs
            ~ₕ comp p n k ts (comp p m n us vs)
  p∘<a,t> : ∀ {m n} (u : UcwfTm m) (us : HomCwf m n)
               → us ~ₕ comp m (suc n)  n (p  n) (m , n < us , u >)
  <a,t>∘s : ∀ {m n} (t : UcwfTm n) (ts : HomCwf n m) (us : HomCwf m n)
            → comp m n (suc m) (n , m < ts , t >) us
              ~ₕ (m , m < comp m n m ts us , sub m n t us >) 
  sym~ₕ : ∀ {m n} {h : HomCwf m n} {t : HomCwf m n} → h ~ₕ t → t ~ₕ h
  trans~ₕ : ∀ {m n} {h t v : HomCwf m n} → h ~ₕ t → t ~ₕ v → h ~ₕ v
  cong~ₕ : ∀ {m n k p} (f : HomCwf m n → HomCwf k p) {h u : HomCwf m n}
             → h ~ₕ u → f h ~ₕ f u
  congt~ₕ : ∀ {m n} (f : UcwfTm m → HomCwf m n) {t u : UcwfTm m}
             → t ~ₜ u → f t ~ₕ f u

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
