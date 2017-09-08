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
data _U~_ : ∀ {n} → UcwfTm n → UcwfTm n → Set where
 subId : ∀ {n} (u : UcwfTm n) → u U~ sub n n u (id n)
 q[<a,t>] : ∀ {m n ts t} → t U~ sub n (suc m) (q m) (n , m < ts , t >)
 ∘sub : ∀ {m n} → ∀ {t ts us} → sub m n t ((comp m n n ts us))
         U~ sub m n (sub n n t ts) us
 symU~ : ∀ {n} (u : UcwfTm n) (u′ : UcwfTm n) → u U~ u′ → u′ U~ u
 transU~ : ∀ {m} (t : UcwfTm m) (u : UcwfTm m) (v : UcwfTm m) →
             t U~ u → u U~ v → t U~ v

reflU~ : ∀ {n} → (u : UcwfTm n) → u U~ u
reflU~ (q n) =
  transU~ (q n) (sub (suc n) (suc n) (q n) (id (suc n))) (q n)
    (subId (q n))
    (symU~ (q n) (sub (suc n) (suc n) (q n) (id (suc n)))
    (subId (q n)))
reflU~ (sub m n u x) =
  transU~ (sub m n u x) (sub m m (sub m n u x) (id m)) (sub m n u x)
    (subId (sub m n u x))
    (symU~ (sub m n u x) (sub m m (sub m n u x) (id m))
    (subId (sub m n u x)))

infix 10 _H~_
data _H~_ : ∀ {n m} → HomCwf n m → HomCwf n m → Set where 
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
  symH~ : ∀ {m n} (h : HomCwf m n) (t : HomCwf m n) → h H~ t → t H~ h
  transH~ : ∀ {m n} (h : HomCwf m n) (t : HomCwf m n) (v : HomCwf m n)
              → h H~ t → t H~ v → h H~ v

reflH~ : ∀ {n m} → (h : HomCwf m n) → h H~ h
reflH~ (id m) =
  transH~ (id m) (comp m m m (id m) (id m)) (id m)
    (symH~ (comp m m m (id m) (id m)) (id m) (∘lid (id m)))
    (∘lid (id m))
reflH~ (comp m n k h h₁) =
  transH~ (comp m n k h h₁) (comp m k k (id k) (comp m n k h h₁))
    (comp m n k h h₁)
    (symH~ (comp m k k (id k) (comp m n k h h₁)) (comp m n k h h₁)
    (∘lid (comp m n k h h₁)))
    (∘lid (comp m n k h h₁))
reflH~ (p n) =
  transH~ (p n) (comp (suc n) n n (id n) (p n)) (p n)
    (symH~ (comp (suc n) n n (id n) (p n)) (p n) (∘lid (p n)))
    (∘lid (p n))
reflH~ (<> m) =
  transH~ (<> m) (comp m m zero (<> m) (id m)) (<> m)
    (symH~ (comp m m zero (<> m) (id m)) (<> m) (∘rid (<> m)))
    (∘<> (id m))
reflH~ (m , n < h , x >) =
  transH~ (m , n < h , x >)
    (comp m (suc n) (suc n) (id (suc n)) (m , n < h , x >))
    (m , n < h , x >)
    (symH~ (comp m (suc n) (suc n) (id (suc n)) (m , n < h , x >))
    (m , n < h , x >) (∘lid (m , n < h , x >)))
    (∘lid (m , n < h , x >))
