module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)

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

infix 10 _U~_
data _U~_ : ∀ {n m} → UcwfTm n → UcwfTm m → Set where
 subId : ∀ {n} (u : UcwfTm n) → u U~ sub n n u (id n)
 q[<a,t>] : ∀ {m n ts t} → t U~ sub n (suc m) (q m) (n , m < ts , t >)
 ∘sub : ∀ {m n} → ∀ {t ts us} → sub m n t ((comp m n n ts us))
         U~ sub m n (sub n n t ts) us

infix 10 _H~_
data _H~_ : ∀ {n m k p} → HomCwf n m → HomCwf k p → Set where 
  id₀ : id zero H~ <> zero
  ∘<> : ∀ {m n} (ts : HomCwf m n) → comp m n zero (<> n) ts H~ <> m
  id<p,q> : ∀ {n} → id (suc n) H~ suc n , n < p n , q n >
  ∘lid : ∀ {m n} (ts : HomCwf m n) → comp m n n (id n) ts H~ ts
  ∘rid : ∀ {m n} (ts : HomCwf m n) → comp m m n ts (id m) H~ ts
  ∘asso : ∀ {m n k p} (ts : HomCwf n k) (us : HomCwf m n) (vs : HomCwf p m) →
            comp p m k (comp m n k ts us) vs
            H~ comp p n k ts (comp p m n us vs)
  p∘<a∘t> : ∀ {m n} (u : UcwfTm m) (us : HomCwf m n)
               → us H~ comp m (suc n)  n (p  n) (m , n < us , u >)
  <a,t>∘s : ∀ {m n} (t : UcwfTm n) (ts : HomCwf n m) (us : HomCwf m n)
            → comp m n (suc m) (n , m < ts , t >) us
              H~ (m , m < comp m n m ts us , sub m n t us >) 
