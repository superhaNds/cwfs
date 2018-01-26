------------------------------------------------------------------------------------
-- An initial Ucwf object with extra structure in which everything is explicit
-- in the sense they are part of the language as constructors. Following the
-- generalized algebraic theory of cwfs, it yields a variable free calculus
-- of explicit substitutions
------------------------------------------------------------------------------------

module Unityped.UcwfModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
import Data.Nat.Properties.Simple as NatP
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Unityped.Ucwf
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------------------
-- The mutually recursive terms and substitutions as data types that form
-- a ucwf object with extra structure

data Tm : Nat → Set
data Sub : Nat → Nat → Set

data Tm where

  -- last variable

  q : ∀ {n} → Tm (suc n)

  -- explicit substitution

  _[_] : ∀ {m n} → Tm n → Sub m n → Tm m

  -- λ abstraction

  lam : ∀ {n} → Tm (suc n) → Tm n

  -- function application
 
  app : ∀ {n} → Tm n → Tm n → Tm n

-- Sub m n corresponds to substitutions of length n of Tms with at most
-- m free variables

-- These represent the morphisms of the base category

infix 8 _∘_

data Sub where

  -- identity substitution

  id : ∀ {m} → Sub m m

  -- composition of substitution

  _∘_ : ∀ {m n k} → Sub n k → Sub m n → Sub m k

  -- empty substitution (terminal object)

  <> : ∀ {m} → Sub m zero

  -- extending a substitution

  <_,_> : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)

  -- projection substitution

  p : ∀ {n} → Sub (suc n) n

weaken : ∀ {n} → Tm n → Tm (suc n)
weaken {n} t = t [ p ] 

⇑_ : ∀ {m n} → Sub m n →  Sub (suc m) (suc n)
⇑_ ts = < ts ∘ p , q >

p′ : (m n : Nat) → Sub (m + n) n
p′ zero n    = id
p′ (suc m) n = p′ m n ∘ p

record Subable (H : Nat → Nat → Set) : Set where
  field
    id-able  : (m : Nat) → H m m
    _∘-able_ : ∀ {m n k} → H n k → H m n → H m k
    p-able   : (n : Nat) → H (suc n) n

suc-homable : ∀ {H} → Subable H → Subable (λ m n → H (suc m) (suc n))
suc-homable Subable = record
  { id-able  = λ m → id-able (suc m)
  ; _∘-able_ = _∘-able_
  ; p-able   = λ m → p-able (suc m)
  } where open Subable Subable

p2-go : ∀ {H} → Subable H → (m : Nat) → H m 0
p2-go homable  zero   = id-able 0 where
  open Subable homable
p2-go homable (suc m) = p-able 0 ∘-able p2-go (suc-homable homable) m where
  open Subable homable

plus-homable-hom : ∀ k → Subable (λ m n → Sub (m + k) (n + k))
plus-homable-hom k = record
  { id-able  = λ n → id {n + k}
  ; _∘-able_ = _∘_
  ; p-able   = λ n → p {n + k}
  }

p1 : (m n : Nat) → Sub (m + n) n
p1 zero n    = id
p1 (suc m) n = p1 m n ∘ p

p2 : (m n : Nat) → Sub (m + n) n
p2 m n = p2-go (plus-homable-hom n) m

------------------------------------------------------------------------------------
-- The inductive relations that specify the Ucwf axioms regardings Subs and terms

infix 5 _≈_
infix 5 _≋_

data _≈_ : ∀ {n} → Tm n → Tm n → Set
data _≋_ : ∀ {n m} → Sub n m → Sub n m → Set

data _≈_  where
  
  subId  : ∀ {n} (t : Tm n) → t [ id ] ≈ t
             
  qCons : ∀ {m n} (ts : Sub n m) t → q [ < ts , t > ] ≈ t
             
  subComp : ∀ {m n k} (ts : Sub k n) (us : Sub m k) t →
             t [ ts ∘ us ] ≈ t [ ts ] [ us ]
  
  subApp : ∀ {n m} (ts : Sub m n) t u →
            app (t [ ts ]) (u [ ts ]) ≈ app t u [ ts ]
             
  subLam : ∀ {n m} (ts : Sub m n) t →
            lam t [ ts ] ≈ lam (t [ ⇑ ts ])

  β : ∀ {n} {t : Tm (suc n)} {u : Tm n} → app (lam t) u ≈ t [ < id , u > ]
             
  η : ∀ {n} {t : Tm n} → lam (app (weaken t) q) ≈ t
  
  sym≈ : ∀ {n} {u u′ : Tm n} →
          u ≈ u′ →
          u′ ≈ u
             
  trans≈ : ∀ {m} {t u v : Tm m} →
            t ≈ u →
            u ≈ v →
            t ≈ v
             
  cong-app : ∀ {n} {t u t′ u′ : Tm n} →
              t ≈ t′ →
              u ≈ u′ →
              app t u ≈ app t′ u′
               
  cong-sub : ∀ {m n} {t u : Tm n} {ts us : Sub m n} →
              t ≈ u →
              ts ≋ us →
              t [ ts ] ≈ u [ us ]
             
  cong-lam : ∀ {n} {t u : Tm (1 + n)} →
              t ≈ u →
              lam t ≈ lam u

refl≈ : ∀ {n} {u : Tm n} → u ≈ u
refl≈ {u = u} = trans≈ (sym≈ (subId u)) (subId u)

data _≋_ where
  
  id₀ : id {0} ≋ <>
  
  <>Lzero : ∀ {m n} (ts : Sub m n) → <> ∘ ts ≋ <>
             
  idExt : ∀ {n} → id {suc n} ≋ < p , q >
             
  idL : ∀ {m n} (ts : Sub m n) → id ∘ ts ≋ ts
             
  idR : ∀ {m n} (ts : Sub m n) → ts ∘ id ≋ ts
             
  assoc : ∀ {m n k p} (ts : Sub n k) (us : Sub m n) (vs : Sub p m) →
           (ts ∘ us) ∘ vs ≋ ts ∘ (us ∘ vs)
             
  pCons : ∀ {m n} (us : Sub m n) u → p ∘ < us , u > ≋ us
             
  compExt : ∀ {m n k} (ts : Sub n k) (us : Sub m n) t →
             < ts , t > ∘ us  ≋ < ts ∘ us , t [ us ] >

  -- Symmetry, transitivity, and congruence
  
  sym≋ : ∀ {m n} {h : Sub m n} {t : Sub m n} →
          h ≋ t →
          t ≋ h
              
  trans≋  : ∀ {m n} {h t v : Sub m n} →
             h ≋ t →
             t ≋ v →
             h ≋ v
              
  cong-<,> : ∀ {m n} {ts us : Sub m n} {t u} →
              t ≈ u →
              ts ≋ us →
              < ts , t > ≋ < us , u >
              
  cong-∘ : ∀ {m n k} {ts vs : Sub n k} {us zs : Sub m n} →
            ts ≋ vs →
            us ≋ zs →
            ts ∘ us ≋ vs ∘ zs             

------------------------------------------------------------------------------------
-- The relations are equivalence ones, plus setoid instances

refl≋ : ∀ {n m} {h : Sub m n} → h ≋ h
refl≋ = trans≋ (sym≋ (idL _)) (idL _)

≈equiv : ∀ {n} → IsEquivalence (_≈_ {n})
≈equiv = record { refl  = refl≈
                 ; sym   = sym≈
                 ; trans = trans≈ }

TmSetoid : ∀ {n} → Setoid _ _
TmSetoid {n} =
  record { Carrier = Tm n
         ; _≈_ = _≈_
         ; isEquivalence = ≈equiv }

≋equiv : ∀ {n m} → IsEquivalence (_≋_ {n} {m})
≋equiv = record { refl  = refl≋
                 ; sym   = sym≋
                 ; trans = trans≋ }
                 
SubSetoid : ∀ {n m} → Setoid _ _
SubSetoid {n} {m} =
  record { Carrier = Sub m n
         ; _≈_ = _≋_
         ; isEquivalence = ≋equiv }

------------------------------------------------------------------------------------
-- Some theorems using the axiomatization

-- there is a terminal arrow from any n to 0

ter-arrow : ∀ {n} (ts : Sub n 0) → ts ≋ <>
ter-arrow ts = begin
  ts           ≈⟨ sym≋ (idL ts) ⟩
  id {0} ∘ ts  ≈⟨ cong-∘ id₀ refl≋ ⟩
  <> ∘ ts      ≈⟨ <>Lzero ts ⟩ 
  <>           ∎
  where open EqR (SubSetoid {0} {_})

-- surjective pairing

surj-<,> : ∀ {n m} (ts : Sub m (1 + n)) → ts ≋ < p ∘ ts , q [ ts ] >
surj-<,> ts = begin
  ts                      ≈⟨ sym≋ (idL ts) ⟩
  id ∘ ts                 ≈⟨ cong-∘ idExt refl≋  ⟩
  < p , q > ∘ ts          ≈⟨ compExt p ts q ⟩
  < p ∘ ts , q [ ts ] >   ∎
  where open EqR (SubSetoid {_} {_})

qLift : ∀ {m n} (ts : Sub m n) → q [ ⇑ ts ] ≈ q
qLift ts = qCons (ts ∘ p) q

qLift₂ : ∀ {m n k} (s : Sub m n)
           (t : Sub k (suc m)) → q [ (⇑ s) ∘ t ] ≈ q [ t ]
qLift₂ s t = begin
  q [ (⇑ s) ∘ t ]                  ≈⟨ refl≈ ⟩
  q [ < s ∘ p , q > ∘ t ]          ≈⟨ cong-sub refl≈ (compExt (s ∘ p) t q) ⟩
  q [ < (s ∘ p) ∘ t , q [ t ] > ]  ≈⟨ qCons ((s ∘ p) ∘ t) (q [ t ]) ⟩ 
  q [ t ]                          ∎
  where open EqR (TmSetoid {_})

------------------------------------------------------------------------------------
-- The pair (Tm, Sub) is a ucwf, λ-ucwf, and λ-βη-ucwf

Tm-Ucwf : Ucwf
Tm-Ucwf = record
            { Tm = Tm
            ; Sub = Sub
            ; _≈_ = _≈_
            ; _≋_ = _≋_
            ; IsEquivT = ≈equiv
            ; IsEquivS = ≋equiv
            ; id = id
            ; _∘_ = _∘_
            ; _[_] = _[_]
            ; <> = <>
            ; <_,_> = <_,_>
            ; p = p
            ; q = q
            ; id₀ = id₀
            ; <>Lzero = <>Lzero
            ; idExt = idExt
            ; idL = idL
            ; idR = idR
            ; assoc = assoc
            ; subId = subId
            ; pCons = pCons
            ; qCons = qCons
            ; subComp = subComp
            ; compExt = compExt
            ; cong-<,> = cong-<,>
            ; cong-sub = cong-sub
            ; cong-∘ = cong-∘
            }

Tm-λ-ucwf : Lambda-ucwf
Tm-λ-ucwf = record
              { ucwf = Tm-Ucwf
              ; lam = lam
              ; app = app
              ; subApp = subApp
              ; subLam = subLam
              ; cong-lam = cong-lam
              ; cong-app = cong-app
              }

Tm-λβη-ucwf : Lambda-βη-ucwf
Tm-λβη-ucwf = record
                { lambda-ucwf = Tm-λ-ucwf
                ; β = β
                ; η = η
                }
