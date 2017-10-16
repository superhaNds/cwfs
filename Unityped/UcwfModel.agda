------------------------------------------------------------------------------------
-- The model of the initial Ucwf object in which everything is explicit
-- in the sense they are part of the language as constructors, similar
-- to the λσ calculus.
------------------------------------------------------------------------------------

module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
import Data.Nat.Properties.Simple as NatP
open import Relation.Binary using (IsEquivalence ; Setoid)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------------------
-- The mutually recursive terms and homs as data types

data CwfTm : Nat → Set
data Hom : Nat → Nat → Set

data CwfTm where
  q    : {n : Nat} → CwfTm (suc n)
  _[_] : {m n : Nat} → CwfTm n → Hom m n → CwfTm m
  lam  : {n : Nat} → CwfTm (suc n) → CwfTm n
  app  : {n : Nat} → CwfTm n → CwfTm n → CwfTm n

-- Hom m n corresponds to substitutions of length n of Terms with at most
-- m free variables

data Hom where
  id    : (m : Nat) → Hom m m
  _∘_   : {m n k : Nat} → Hom n k → Hom m n → Hom m k
  p     : (n : Nat) → Hom (suc n) n
  <>    : {m : Nat} → Hom m zero
  <_,_> : {m n : Nat} → Hom m n → CwfTm m → Hom m (suc n)

weaken : ∀ {n} → CwfTm n → CwfTm (suc n)
weaken t = t [ p _ ]

⇑_ : ∀ {m n} → Hom m n →  Hom (suc m) (suc n)
⇑_ ts = < ts ∘ p _ , q >

p′ : (m n : Nat) → Hom (m + n) n
p′ zero n    = id n
p′ (suc m) n = p′ m n ∘ p (m + n)

p′′ : (m n : Nat) → Hom (m + n) n
p′′ zero n = id n
p′′ (suc m) n rewrite P.sym (NatP.+-suc m n) = p n ∘ p′′ m (1 + n)

------------------------------------------------------------------------------------
-- The inductive relations that specify the Ucwf axioms regardings Homs and terms

infix 10 _~ₜ_
infix 10 _~ₕ_

data _~ₜ_ : ∀ {n} → CwfTm n → CwfTm n → Set
data _~ₕ_ : ∀ {n m} → Hom n m → Hom n m → Set

data _~ₜ_  where

  -- Ucwf laws
  
  termId  : ∀ {n} (u : CwfTm n) → u ~ₜ u [ (id n) ]
  qCons   : ∀ {m n} (t : CwfTm n) (ts : Hom n m) → t ~ₜ q [ < ts , t > ]
  clos    : ∀ {m n k} (t : CwfTm n) (ts : Hom k n) (us : Hom m k) → t [ ts ∘ us ] ~ₜ  (t [ ts ])[ us ]

  -- β and η laws
  
  β       : ∀ {n} (t : CwfTm (suc n)) (u : CwfTm n) → app (lam t) u ~ₜ t [ < id n , u > ]
  η       : ∀ {n} (t : CwfTm n) → lam (app (t [ p n ]) q) ~ₜ t

  -- Substituting an application
  
  appCm   : ∀ {n m} (t : CwfTm n) (u : CwfTm n) (ts : Hom m n) →
            app (t [ ts ]) (u [ ts ]) ~ₜ app t u [ ts ]
            
  -- Substituting a lambda expression
  
  lamCm   : ∀ {n m} (t : CwfTm (suc n)) (ts : Hom m n) → lam t [ ts ] ~ₜ lam (t [ ⇑ ts ])

  -- Symmetry, transitivity, and congruence
  
  sym~ₜ   : ∀ {n} {u u′ : CwfTm n} → u ~ₜ u′ → u′ ~ₜ u
  trans~ₜ : ∀ {m} {t u v : CwfTm m} → t ~ₜ u → u ~ₜ v → t ~ₜ v
  cong~ₜ  : ∀ {m n} (f : CwfTm m → CwfTm n) {h u : CwfTm m} → h ~ₜ u → f h ~ₜ f u
  congh~ₜ : ∀ {m n k} (f : Hom m n → CwfTm k) {h v : Hom m n} → h ~ₕ v → f h ~ₜ f v

refl~ₜ : ∀ {n} {u : CwfTm n} → u ~ₜ u
refl~ₜ = trans~ₜ (termId _) (sym~ₜ (termId _))

data _~ₕ_ where

  -- Ucwf laws
  
  id₀     : id 0 ~ₕ <>
  ∘<>     : ∀ {m n} (ts : Hom m n) → (<> ∘ ts) ~ₕ <>
  varp    : ∀ {n} → id (suc n) ~ₕ < p n , q >
  idL     : ∀ {m n} (ts : Hom m n) → (id n) ∘ ts ~ₕ ts
  idR     : ∀ {m n} (ts : Hom m n) → ts ∘ (id m) ~ₕ ts
  assoc   : ∀ {m n k p} (ts : Hom n k) (us : Hom m n) (vs : Hom p m) →
            (ts ∘ us) ∘ vs  ~ₕ ts ∘ (us ∘ vs)
  pCons   : ∀ {m n} (u : CwfTm m) (us : Hom m n) → us ~ₕ (p  n) ∘ < us , u >
  maps    : ∀ {m n k} (t : CwfTm n) (ts : Hom n k) (us : Hom m n) →
            < ts , t > ∘ us  ~ₕ < ts ∘ us , t [ us ] >

  -- Symmetry, transitivity, and congruence
  
  sym~ₕ   : ∀ {m n} {h : Hom m n} {t : Hom m n} → h ~ₕ t → t ~ₕ h
  trans~ₕ : ∀ {m n} {h t v : Hom m n} → h ~ₕ t → t ~ₕ v → h ~ₕ v
  cong~ₕ  : ∀ {m n k p} (f : Hom m n → Hom k p) {h u : Hom m n} → h ~ₕ u → f h ~ₕ f u
  congt~ₕ : ∀ {m n} (f : CwfTm m → Hom m n) {t u : CwfTm m} → t ~ₜ u → f t ~ₕ f u

------------------------------------------------------------------------------------
-- The relations are equivalence ones, plus setoid instances

refl~ₕ : ∀ {n m} {h : Hom m n} → h ~ₕ h
refl~ₕ = trans~ₕ (sym~ₕ (idL _)) (idL _)

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

------------------------------------------------------------------------------------
-- Some theorems using the axiomatization

hom0~<> : ∀ {n} (ts : Hom n 0) → ts ~ₕ <>
hom0~<> ts = begin
  ts         ≈⟨ sym~ₕ (idL ts) ⟩
  id 0 ∘ ts  ≈⟨ cong~ₕ (_∘ ts) id₀ ⟩
  <> ∘ ts    ≈⟨ ∘<> ts ⟩ 
  <>         ∎
  where open EqR (HomS {0} {_})

p′0~<> : ∀ {m} → p′ m 0 ~ₕ <>
p′0~<> {m} = hom0~<> (p′ m 0)

p′′0~<> : ∀ {m} → p′′ m 0 ~ₕ <>
p′′0~<> {m} = hom0~<> (p′′ m 0)

postulate p′isp : ∀ m n → p′ m n ~ₕ p′′ m n

-- p′ m n ∘ p (m + n)
-- p n ∘ p′′ m (1 + n)
{-
pp′ : ∀ m n → p′ m n ~ₕ p′′ m n
pp′ zero n = cong~ₕ (λ _ → id n) id₀
pp′ (suc m) n = {!!}
-}

eta : ∀ {n m} (ts : Hom m (1 + n)) → ts ~ₕ < p n ∘ ts , q [ ts ] >
eta ts = begin
  ts                        ≈⟨ sym~ₕ (idL ts) ⟩
  id _ ∘ ts                 ≈⟨ cong~ₕ (_∘ ts) varp  ⟩
  < p _ , q > ∘ ts          ≈⟨ maps q (p _) ts ⟩
  < p _ ∘ ts , q [ ts ] >   ∎
  where open EqR (HomS {_} {_})

qLift : ∀ {m n} (ts : Hom m n) → q [ ⇑ ts ] ~ₜ q
qLift ts = sym~ₜ (qCons q (ts ∘ p _))

qLift₂ : ∀ {m n k} (s : Hom m n) (t : Hom k (suc m)) → q [ (⇑ s) ∘ t ] ~ₜ q [ t ]
qLift₂ s t = begin
  q [ (⇑ s) ∘ t ]                    ≈⟨ refl~ₜ ⟩
  q [ < s ∘ p _ , q > ∘ t ]          ≈⟨ congh~ₜ (_[_] q) (maps q (s ∘ p _) t) ⟩
  q [ < (s ∘ p _) ∘ t , q [ t ] > ]  ≈⟨ sym~ₜ (qCons (q [ t ]) ((s ∘ p _) ∘ t)) ⟩ 
  q [ t ]                            ∎
  where open EqR (CwfTmS {_})
