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

  -- variable with index 0

  q    : {n : Nat} → Term (suc n)

  -- explicit substitution

  _[_] : {m n : Nat} → Term n → Hom m n → Term m

  -- λ abstraction

  lam  : {n : Nat} → Term (suc n) → Term n

  -- function application
 
  app  : {n : Nat} → Term n → Term n → Term n

-- Hom m n corresponds to substitutions of length n of Terms with at most
-- m free variables

data Hom where

  -- identity substitution

  id    : {m : Nat} → Hom m m

  -- projection substitution

  p     : {n : Nat} → Hom (suc n) n

  -- composition of substitution

  _∘_   : {m n k : Nat} → Hom n k → Hom m n → Hom m k

  -- empty substitution (terminal object)

  <>    : {m : Nat} → Hom m zero

  -- extending a substitution

  <_,_> : {m n : Nat} → Hom m n → Term m → Hom m (suc n)

weaken : ∀ {n} → Term n → Term (suc n)
weaken {n} t = t [ p ] 

⇑_ : ∀ {m n} → Hom m n →  Hom (suc m) (suc n)
⇑_ ts = < ts ∘ p , q >

p′ : (m n : Nat) → Hom (m + n) n
p′ zero n    = id
p′ (suc m) n = p′ m n ∘ p

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

infix 10 _~_
infix 10 _~~_

data _~_ : ∀ {n} → Term n → Term n → Set
data _~~_ : ∀ {n m} → Hom n m → Hom n m → Set

data _~_  where

  -- Ucwf laws
  
  termId  : ∀ {n} (u : Term n) →
             u ~ u [ id ]
             
  qCons   : ∀ {m n} (t : Term n) (ts : Hom n m) →
             t ~ q [ < ts , t > ]
             
  clos    : ∀ {m n k} (t : Term n) (ts : Hom k n) (us : Hom m k) →
             t [ ts ∘ us ] ~  (t [ ts ])[ us ]

  -- β and η
  
  β       : ∀ {n} (t : Term (suc n)) (u : Term n) →
             app (lam t) u ~ t [ < id , u > ]
             
  η       : ∀ {n} (t : Term n) →
             lam (app (t [ p ]) q) ~ t

  -- Substituting an application
  
  appCm   : ∀ {n m} (t : Term n) (u : Term n) (ts : Hom m n) →
             app (t [ ts ]) (u [ ts ]) ~ app t u [ ts ]
            
  -- Substituting a lambda expression
  
  lamCm   : ∀ {n m} (t : Term (suc n)) (ts : Hom m n) →
             lam t [ ts ] ~ lam (t [ ⇑ ts ])

  -- Symmetry, transitivity, and congruence
  
  sym~    : ∀ {n} {u u′ : Term n} →
             u ~ u′ →
             u′ ~ u
             
  trans~  : ∀ {m} {t u v : Term m} →
             t ~ u →
             u ~ v →
             t ~ v
             
  cong-app  : ∀ {n} {t u t′ u′ : Term n} →
               t ~ t′ →
               u ~ u′ →
               app t u ~ app t′ u′
               
  cong-[] : ∀ {m n} {t u : Term n} {ts us : Hom m n} →
             t ~ u →
             ts ~~ us →
             t [ ts ] ~ u [ us ]
             
  cong-lam    : ∀ {n} {t u : Term (1 + n)} →
                t ~ u →
                lam t ~ lam u

refl~ : ∀ {n} {u : Term n} → u ~ u
refl~ = trans~ (termId _) (sym~ (termId _))

data _~~_ where

  -- Ucwf laws
  
  id₀     : id {0} ~~ <>
  
  ∘<>     : ∀ {m n} (ts : Hom m n) →
             <> ∘ ts ~~ <>
             
  varp    : ∀ {n} →
             id {suc n} ~~ < p , q >
             
  idL     : ∀ {m n} (ts : Hom m n) →
             id ∘ ts ~~ ts
             
  idR     : ∀ {m n} (ts : Hom m n) →
             ts ∘ id ~~ ts
             
  assoc   : ∀ {m n k p} (ts : Hom n k) (us : Hom m n) (vs : Hom p m) →
             (ts ∘ us) ∘ vs  ~~ ts ∘ (us ∘ vs)
             
  pCons   : ∀ {m n} (u : Term m) (us : Hom m n) →
             us ~~ p ∘ < us , u >
             
  maps    : ∀ {m n k} (t : Term n) (ts : Hom n k) (us : Hom m n) →
             < ts , t > ∘ us  ~~ < ts ∘ us , t [ us ] >

  -- Symmetry, transitivity, and congruence
  
  sym~~    : ∀ {m n} {h : Hom m n} {t : Hom m n} →
              h ~~ t →
              t ~~ h
              
  trans~~  : ∀ {m n} {h t v : Hom m n} →
              h ~~ t →
              t ~~ v →
              h ~~ v
              
  cong-<,> : ∀ {m n} {t u : Term m} {ts us : Hom m n} →
              t ~ u →
              ts ~~ us →
              < ts , t > ~~ < us , u >
              
  cong-∘   : ∀ {m n k} {ts vs : Hom n k} {us zs : Hom m n} →
              ts ~~ vs →
              us ~~ zs →
              ts ∘ us ~~ vs ∘ zs             

------------------------------------------------------------------------------------
-- The relations are equivalence ones, plus setoid instances

refl~~ : ∀ {n m} {h : Hom m n} → h ~~ h
refl~~ = trans~~ (sym~~ (idL _)) (idL _)

~equiv : ∀ {n} → IsEquivalence (_~_ {n})
~equiv = record { refl  = refl~
                 ; sym   = sym~
                 ; trans = trans~ }

TermS : ∀ {n} → Setoid _ _
TermS {n} =
  record { Carrier = Term n
         ; _≈_ = _~_
         ; isEquivalence = ~equiv }

~~equiv : ∀ {n m} → IsEquivalence (_~~_ {n} {m})
~~equiv = record { refl  = refl~~
                 ; sym   = sym~~
                 ; trans = trans~~ }
                 
HomS : ∀ {n m} → Setoid _ _
HomS {n} {m} =
  record { Carrier = Hom m n
         ; _≈_ = _~~_
         ; isEquivalence = ~~equiv }

------------------------------------------------------------------------------------
-- Some theorems using the axiomatization

hom0~<> : ∀ {n} (ts : Hom n 0) → ts ~~ <>
hom0~<> ts = begin
  ts           ≈⟨ sym~~ (idL ts) ⟩
  id {0} ∘ ts  ≈⟨ cong-∘ id₀ refl~~ ⟩
  <> ∘ ts      ≈⟨ ∘<> ts ⟩ 
  <>           ∎
  where open EqR (HomS {0} {_})

p′0~<> : ∀ {m} → p′ m 0 ~~ <>
p′0~<> {m} = hom0~<> (p′ m 0)

eta : ∀ {n m} (ts : Hom m (1 + n)) → ts ~~ < p ∘ ts , q [ ts ] >
eta ts = begin
  ts                      ≈⟨ sym~~ (idL ts) ⟩
  id ∘ ts                 ≈⟨ cong-∘ varp refl~~  ⟩
  < p , q > ∘ ts          ≈⟨ maps q p ts ⟩
  < p ∘ ts , q [ ts ] >   ∎
  where open EqR (HomS {_} {_})

qLift : ∀ {m n} (ts : Hom m n) → q [ ⇑ ts ] ~ q
qLift ts = sym~ (qCons q (ts ∘ p))

qLift₂ : ∀ {m n k} (s : Hom m n) (t : Hom k (suc m)) → q [ (⇑ s) ∘ t ] ~ q [ t ]
qLift₂ s t = begin
  q [ (⇑ s) ∘ t ]                  ≈⟨ refl~ ⟩
  q [ < s ∘ p , q > ∘ t ]          ≈⟨ cong-[] refl~ (maps q (s ∘ p) t) ⟩
  q [ < (s ∘ p) ∘ t , q [ t ] > ]  ≈⟨ sym~ (qCons (q [ t ]) ((s ∘ p) ∘ t)) ⟩ 
  q [ t ]                          ∎
  where open EqR (TermS {_})

------------------------------------------------------------------------------------
-- The term model is trivially a ucwf

Tm-Ucwf : Ucwf
Tm-Ucwf = record
            { Term  = Term
            ; Hom   = Hom
            ; _~_  = _~_
            ; _~~_  = _~~_
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
            ; terId = λ t → sym~ (termId t)
            ; pCons = λ t ts → sym~~ (pCons t ts)
            ; qCons = λ t ts → sym~ (qCons t ts)
            ; clos  = clos
            ; maps  = maps
            ; cong-<,> = cong-<,>
            ; cong-[_] = cong-[]
            ; cong-∘   = cong-∘
            }

Tm-λ$-ucwf : Lambda-ucwf
Tm-λ$-ucwf = record
               { ucwf   = Tm-Ucwf
               ; ƛ      = lam
               ; _·_    = app
               ; cong-ƛ = cong-lam
               ; cong-· = cong-app
               ; app    = appCm
               ; abs    = lamCm
               }

Tm-λβη-ucwf : Lambda-βη-ucwf
Tm-λβη-ucwf = record
                { lambda-ucwf = Tm-λ$-ucwf
                ; β = β
                ; η = η
                }
