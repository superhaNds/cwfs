module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Relation.Binary using (IsEquivalence)

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

weaken : ∀ {n : Nat} → UcwfTm n → UcwfTm (suc n)
weaken {n} t = sub (suc n) n t (p n)

infix 10 _~ₜ_
data _~ₜ_ : ∀ {n} (u₁ u₂ : UcwfTm n) → Set where
 subId : ∀ {n} (u : UcwfTm n) → u ~ₜ sub n n u (id n)
 q[<a,t>] : ∀ {m n ts t} → t ~ₜ sub n (suc m) (q m) (n , m < ts , t >)
 ∘sub : ∀ {m n} → ∀ {t ts us} → sub m n t ((comp m n n ts us))
         ~ₜ sub m n (sub n n t ts) us
 sym~ₜ : ∀ {n} (u : UcwfTm n) (u′ : UcwfTm n) → u ~ₜ u′ → u′ ~ₜ u
 trans~ₜ : ∀ {m} (t : UcwfTm m) (u : UcwfTm m) (v : UcwfTm m) →
             t ~ₜ u → u ~ₜ v → t ~ₜ v

refl~ₜ : ∀ {n} (u : UcwfTm n) → u ~ₜ u
refl~ₜ u = trans~ₜ u (sub _ _ u (id _)) u (subId u)
             (sym~ₜ u (sub _ _ u (id _)) (subId u))

~ₜequiv : ∀ {n : Nat} → IsEquivalence (_~ₜ_ {n})
~ₜequiv = record { refl  = λ {x} → refl~ₜ x
                 ; sym   = λ x → sym~ₜ _ _ x
                 ; trans = λ {i} {j} {k} → trans~ₜ i j k }

infix 10 _~ₕ_
data _~ₕ_ : ∀ {n m} (h₁ h₂ : HomCwf n m) → Set where 
  id₀ : id zero ~ₕ <> zero
  ∘<> : ∀ {m n} (ts : HomCwf m n) → comp m n zero (<> n) ts ~ₕ <> m
  id<p,q> : ∀ {n} → id (suc n) ~ₕ suc n , n < p n , q n >
  ∘lid : ∀ {m n} (ts : HomCwf m n) → comp m n n (id n) ts ~ₕ ts
  ∘rid : ∀ {m n} (ts : HomCwf m n) → comp m m n ts (id m) ~ₕ ts
  ∘asso : ∀ {m n k p} (ts : HomCwf n k) (us : HomCwf m n) (vs : HomCwf p m) →
            comp p m k (comp m n k ts us) vs
            ~ₕ comp p n k ts (comp p m n us vs)
  p∘<a∘t> : ∀ {m n} (u : UcwfTm m) (us : HomCwf m n)
               → us ~ₕ comp m (suc n)  n (p  n) (m , n < us , u >)
  <a,t>∘s : ∀ {m n} (t : UcwfTm n) (ts : HomCwf n m) (us : HomCwf m n)
            → comp m n (suc m) (n , m < ts , t >) us
              ~ₕ (m , m < comp m n m ts us , sub m n t us >) 
  sym~ₕ : ∀ {m n} (h : HomCwf m n) (t : HomCwf m n) → h ~ₕ t → t ~ₕ h
  trans~ₕ : ∀ {m n} (h : HomCwf m n) (t : HomCwf m n) (v : HomCwf m n)
              → h ~ₕ t → t ~ₕ v → h ~ₕ v

refl~ₕ : ∀ {n m} (h : HomCwf m n) → h ~ₕ h
refl~ₕ h = trans~ₕ h (comp _ _ _ (id _) h) h
              (sym~ₕ (comp _ _ _ (id _) h) h (∘lid h)) (∘lid h)

~ₕequiv : ∀ {n m} → IsEquivalence (_~ₕ_ {n} {m})
~ₕequiv = record { refl   = λ {x} → refl~ₕ x
                 ; sym   = λ {i} {j} → sym~ₕ i j
                 ; trans = λ {i} {j} {k} → trans~ₕ i j k }
