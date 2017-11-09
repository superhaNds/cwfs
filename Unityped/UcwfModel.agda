------------------------------------------------------------------------------------
-- The model of the initial Ucwf object in which everything is explicit
-- in the sense they are part of the language as constructors. It is trivially
-- a Ucwf.
------------------------------------------------------------------------------------

module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
import Data.Nat.Properties.Simple as NatP
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Unityped.Ucwf
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------------------
-- The mutually recursive terms and homs as data types which form a Term model of
-- a ucwf

data Term : Nat → Set
data Hom : Nat → Nat → Set

data Term where
  q    : {n : Nat} → Term (suc n)
  _[_] : {m n : Nat} → Term n → Hom m n → Term m
  lam  : {n : Nat} → Term (suc n) → Term n
  app  : {n : Nat} → Term n → Term n → Term n

-- Hom m n corresponds to substitutions of length n of Terms with at most
-- m free variables

data Hom where
  id    : {m : Nat} → Hom m m
  _∘_   : {m n k : Nat} → Hom n k → Hom m n → Hom m k
  p     : {n : Nat} → Hom (suc n) n
  <>    : {m : Nat} → Hom m zero
  <_,_> : {m n : Nat} → Hom m n → Term m → Hom m (suc n)

weaken : ∀ {n} → Term n → Term (suc n)
weaken {n} t = t [ p ] 

⇑_ : ∀ {m n} → Hom m n →  Hom (suc m) (suc n)
⇑_ ts = < ts ∘ p , q >

p′ : (m n : Nat) → Hom (m + n) n
p′ zero n    = id
p′ (suc m) n = p′ m n ∘ p

p′′ : (m n : Nat) → Hom (m + n) n
p′′ zero n = id
p′′ (suc m) n rewrite P.sym (NatP.+-suc m n) = p ∘ p′′ m (1 + n)

record Homable (H : Nat → Nat → Set) : Set where
  field
    id-able  : (m : Nat) → H m m
    _∘-able_ : ∀ {m n k} → H n k → H m n → H m k
    p-able   : (n : Nat) → H (suc n) n

suc-homable : ∀ {H} → Homable H → Homable (λ m n → H (suc m) (suc n))
suc-homable homable = record
  { id-able  = λ m → id-able (suc m)
  ; _∘-able_ = _∘-able_
  ; p-able   = λ m → p-able (suc m)
  } where open Homable homable

p2-go : ∀ {H} → Homable H → (m : Nat) → H m 0
p2-go homable  zero   = id-able 0 where
  open Homable homable
p2-go homable (suc m) = p-able 0 ∘-able p2-go (suc-homable homable) m where
  open Homable homable

plus-homable-hom : ∀ k → Homable (λ m n → Hom (m + k) (n + k))
plus-homable-hom k = record
  { id-able  = λ n → id {n + k}
  ; _∘-able_ = _∘_
  ; p-able   = λ n → p {n + k}
  }

p1 : (m n : Nat) → Hom (m + n) n
p1 zero n    = id
p1 (suc m) n = p1 m n ∘ p

p2 : (m n : Nat) → Hom (m + n) n
p2 m n = p2-go (plus-homable-hom n) m

------------------------------------------------------------------------------------
-- The inductive relations that specify the Ucwf axioms regardings Homs and terms

infix 10 _~ₜ_
infix 10 _~ₕ_

data _~ₜ_ : ∀ {n} → Term n → Term n → Set
data _~ₕ_ : ∀ {n m} → Hom n m → Hom n m → Set

data _~ₜ_  where

  -- Ucwf laws
  
  termId  : ∀ {n} (u : Term n) → u ~ₜ u [ id ]
  qCons   : ∀ {m n} (t : Term n) (ts : Hom n m) → t ~ₜ q [ < ts , t > ]
  clos    : ∀ {m n k} (t : Term n) (ts : Hom k n) (us : Hom m k) → t [ ts ∘ us ] ~ₜ  (t [ ts ])[ us ]

  -- β and η
  
  β       : ∀ {n} (t : Term (suc n)) (u : Term n) → app (lam t) u ~ₜ t [ < id , u > ]
  η       : ∀ {n} (t : Term n) → lam (app (t [ p ]) q) ~ₜ t

  -- Substituting an application
  
  appCm   : ∀ {n m} (t : Term n) (u : Term n) (ts : Hom m n) →
            app (t [ ts ]) (u [ ts ]) ~ₜ app t u [ ts ]
            
  -- Substituting a lambda expression
  
  lamCm   : ∀ {n m} (t : Term (suc n)) (ts : Hom m n) → lam t [ ts ] ~ₜ lam (t [ ⇑ ts ])

  -- Symmetry, transitivity, and congruence
  
  sym~ₜ    : ∀ {n} {u u′ : Term n} → u ~ₜ u′ → u′ ~ₜ u
  trans~ₜ  : ∀ {m} {t u v : Term m} → t ~ₜ u → u ~ₜ v → t ~ₜ v
  cong-[] : ∀ {m n} {t u : Term n} {ts us : Hom m n} → t ~ₜ u → ts ~ₕ us → t [ ts ] ~ₜ u [ us ]
  cong~ₜ   : ∀ {m n} (f : Term m → Term n) {h u : Term m} → h ~ₜ u → f h ~ₜ f u
  congh~ₜ  : ∀ {m n k} (f : Hom m n → Term k) {h v : Hom m n} → h ~ₕ v → f h ~ₜ f v

refl~ₜ : ∀ {n} {u : Term n} → u ~ₜ u
refl~ₜ = trans~ₜ (termId _) (sym~ₜ (termId _))

data _~ₕ_ where

  -- Ucwf laws
  
  id₀     : id {0} ~ₕ <>
  ∘<>     : ∀ {m n} (ts : Hom m n) → (<> ∘ ts) ~ₕ <>
  varp    : ∀ {n} → id {suc n} ~ₕ < p , q >
  idL     : ∀ {m n} (ts : Hom m n) → id ∘ ts ~ₕ ts
  idR     : ∀ {m n} (ts : Hom m n) → ts ∘ id ~ₕ ts
  assoc   : ∀ {m n k p} (ts : Hom n k) (us : Hom m n) (vs : Hom p m) →
            (ts ∘ us) ∘ vs  ~ₕ ts ∘ (us ∘ vs)
  pCons   : ∀ {m n} (u : Term m) (us : Hom m n) → us ~ₕ p ∘ < us , u >
  maps    : ∀ {m n k} (t : Term n) (ts : Hom n k) (us : Hom m n) →
            < ts , t > ∘ us  ~ₕ < ts ∘ us , t [ us ] >

  -- Symmetry, transitivity, and congruence
  
  sym~ₕ    : ∀ {m n} {h : Hom m n} {t : Hom m n} → h ~ₕ t → t ~ₕ h
  trans~ₕ  : ∀ {m n} {h t v : Hom m n} → h ~ₕ t → t ~ₕ v → h ~ₕ v
  cong-<,> : ∀ {m n} {t u : Term m} {ts us : Hom m n} →
             t ~ₜ u → ts ~ₕ us → < ts , t > ~ₕ < us , u >
  cong-∘   : ∀ {m n k} {ts vs : Hom n k} {us zs : Hom m n} →
             ts ~ₕ vs → us ~ₕ zs → ts ∘ us ~ₕ vs ∘ zs             
  cong~ₕ   : ∀ {m n k p} (f : Hom m n → Hom k p) {h u : Hom m n} → h ~ₕ u → f h ~ₕ f u
  congt~ₕ  : ∀ {m n} (f : Term m → Hom m n) {t u : Term m} → t ~ₜ u → f t ~ₕ f u

------------------------------------------------------------------------------------
-- The relations are equivalence ones, plus setoid instances

refl~ₕ : ∀ {n m} {h : Hom m n} → h ~ₕ h
refl~ₕ = trans~ₕ (sym~ₕ (idL _)) (idL _)

~ₜequiv : ∀ {n} → IsEquivalence (_~ₜ_ {n})
~ₜequiv = record { refl  = refl~ₜ
                 ; sym   = sym~ₜ
                 ; trans = trans~ₜ }

TermS : ∀ {n} → Setoid _ _
TermS {n} =
  record { Carrier = Term n
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
  ts           ≈⟨ sym~ₕ (idL ts) ⟩
  id {0} ∘ ts  ≈⟨ cong~ₕ (_∘ ts) id₀ ⟩
  <> ∘ ts      ≈⟨ ∘<> ts ⟩ 
  <>           ∎
  where open EqR (HomS {0} {_})

p′0~<> : ∀ {m} → p′ m 0 ~ₕ <>
p′0~<> {m} = hom0~<> (p′ m 0)

p′′0~<> : ∀ {m} → p′′ m 0 ~ₕ <>
p′′0~<> {m} = hom0~<> (p′′ m 0)

eta : ∀ {n m} (ts : Hom m (1 + n)) → ts ~ₕ < p ∘ ts , q [ ts ] >
eta ts = begin
  ts                      ≈⟨ sym~ₕ (idL ts) ⟩
  id ∘ ts                 ≈⟨ cong~ₕ (_∘ ts) varp  ⟩
  < p , q > ∘ ts          ≈⟨ maps q p ts ⟩
  < p ∘ ts , q [ ts ] >   ∎
  where open EqR (HomS {_} {_})

qLift : ∀ {m n} (ts : Hom m n) → q [ ⇑ ts ] ~ₜ q
qLift ts = sym~ₜ (qCons q (ts ∘ p))

qLift₂ : ∀ {m n k} (s : Hom m n) (t : Hom k (suc m)) → q [ (⇑ s) ∘ t ] ~ₜ q [ t ]
qLift₂ s t = begin
  q [ (⇑ s) ∘ t ]                  ≈⟨ refl~ₜ ⟩
  q [ < s ∘ p , q > ∘ t ]          ≈⟨ congh~ₜ (_[_] q) (maps q (s ∘ p) t) ⟩
  q [ < (s ∘ p) ∘ t , q [ t ] > ]  ≈⟨ sym~ₜ (qCons (q [ t ]) ((s ∘ p) ∘ t)) ⟩ 
  q [ t ]                          ∎
  where open EqR (TermS {_})

------------------------------------------------------------------------------------
-- The term model instantiated as a Ucwf

Tm-Ucwf : Ucwf
Tm-Ucwf = record
            { Term  = Term
            ; Hom   = Hom
            ; _~ₜ_  = _~ₜ_
            ; _~ₕ_  = _~ₕ_
            ; id    = id
            ; <>    = <>
            ; p     = p
            ; q     = q
            ; _∘_   = _∘_
            ; _[_]  = _[_]
            ; <_,_> = <_,_>
            ; id₀   = id₀
            ; ∘<>   = ∘<>
            ; varp  = varp
            ; idL   = idL
            ; idR   = idR
            ; assoc = assoc
            ; terId = λ t → sym~ₜ (termId t)
            ; pCons = λ t ts → sym~ₕ (pCons t ts)
            ; qCons = λ t ts → sym~ₜ (qCons t ts)
            ; clos  = clos
            ; maps  = maps
            ; cong-<,> = cong-<,>
            ; cong-[_] = cong-[]
            ; cong-∘   = cong-∘
            }

Tm-λ$-ucwf : Lambda-ucwf
Tm-λ$-ucwf = record
               { ucwf = Tm-Ucwf
               ; ƛ    = lam
               ; _·_  = app
               ; app  = appCm
               ; abs  = lamCm
               }

Tm-λβη-ucwf : Lambda-βη-ucwf
Tm-λβη-ucwf = record
                { lambda-ucwf = Tm-λ$-ucwf
                ; β = β
                ; η = η
                }
