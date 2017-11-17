module Definitions where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Data.Vec hiding ([_])
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P


-- the ucwf combinator language
-------------------------------------------------------------

data Tm-cwf : Nat → Set
data Hom : Nat → Nat → Set

data Tm-cwf where
  q    : {n : Nat} → Tm-cwf (suc n)
  _[_] : {m n : Nat} → Tm-cwf n → Hom m n → Tm-cwf m

data Hom where
  id    : {m : Nat} → Hom m m
  _∘_   : {m n k : Nat} → Hom n k → Hom m n → Hom m k
  p     : {n : Nat} → Hom (suc n) n
  <>    : {m : Nat} → Hom m zero
  <_,_> : {m n : Nat} → Hom m n → Tm-cwf m → Hom m (suc n)

infix 10 _~_
infix 10 _~~_

data _~_ : ∀ {n} → Tm-cwf n → Tm-cwf n → Set
data _~~_ : ∀ {n m} → Hom n m → Hom n m → Set

data _~_  where
  termId  : ∀ {n} (u : Tm-cwf n) → u ~ u [ id ]
  qCons   : ∀ {m n} (t : Tm-cwf n) (ts : Hom n m) → t ~ q [ < ts , t > ]
  clos    : ∀ {m n k} (t : Tm-cwf n) (ts : Hom k n) (us : Hom m k) → t [ ts ∘ us ] ~  (t [ ts ])[ us ]
  sym~    : ∀ {n} {u u′ : Tm-cwf n} → u ~ u′ → u′ ~ u
  trans~  : ∀ {m} {t u v : Tm-cwf m} → t ~ u → u ~ v → t ~ v
  cong-[] : ∀ {m n} {t u : Tm-cwf n} {ts us : Hom m n} → t ~ u → ts ~~ us → t [ ts ] ~ u [ us ]

refl~ : ∀ {n} {u : Tm-cwf n} → u ~ u
refl~ = trans~ (termId _) (sym~ (termId _))

data _~~_ where
  id₀     : id {0} ~~ <>
  ∘<>     : ∀ {m n} (ts : Hom m n) → (<> ∘ ts) ~~ <>
  varp    : ∀ {n} → id {suc n} ~~ < p , q >
  idL     : ∀ {m n} (ts : Hom m n) → id ∘ ts ~~ ts
  idR     : ∀ {m n} (ts : Hom m n) → ts ∘ id ~~ ts
  assoc   : ∀ {m n k p} (ts : Hom n k) (us : Hom m n) (vs : Hom p m) →
            (ts ∘ us) ∘ vs  ~~ ts ∘ (us ∘ vs)
  pCons   : ∀ {m n} (u : Tm-cwf m) (us : Hom m n) → us ~~ p ∘ < us , u >
  maps    : ∀ {m n k} (t : Tm-cwf n) (ts : Hom n k) (us : Hom m n) →
            < ts , t > ∘ us  ~~ < ts ∘ us , t [ us ] >
  sym~~    : ∀ {m n} {h : Hom m n} {t : Hom m n} → h ~~ t → t ~~ h
  trans~~  : ∀ {m n} {h t v : Hom m n} → h ~~ t → t ~~ v → h ~~ v
  cong-<,> : ∀ {m n} {t u : Tm-cwf m} {ts us : Hom m n} →
             t ~ u → ts ~~ us → < ts , t > ~~ < us , u >
  cong-∘   : ∀ {m n k} {ts vs : Hom n k} {us zs : Hom m n} →
             ts ~~ vs → us ~~ zs → ts ∘ us ~~ vs ∘ zs             

refl~~ : ∀ {n m} {h : Hom m n} → h ~~ h
refl~~ = trans~~ (sym~~ (idL _)) (idL _)

~equiv : ∀ {n} → IsEquivalence (_~_ {n})
~equiv = record { refl  = refl~
                 ; sym   = sym~
                 ; trans = trans~ }

TermS : ∀ {n} → Setoid _ _
TermS {n} =
  record { Carrier = Tm-cwf n
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

hom-0~<> : ∀ {n} (ts : Hom n 0) → ts ~~ <>
hom-0~<> ts = trans~~
   (trans~~ (sym~~ (idL ts))
            (cong-∘ id₀ refl~~))
   (∘<> ts)

surj-<,> : ∀ {n m} (ts : Hom m (suc n)) → ts ~~ < p ∘ ts , q [ ts ] >
surj-<,> ts = trans~~
  (trans~~ (sym~~ (idL ts))
           (cong-∘ varp refl~~))
  (maps q p ts)

-------------------------------------------------------------
-- Wellscoped vars


data Tm (n : Nat) : Set where
  var : (i : Fin n) → Tm n

Ren : Nat → Nat → Set
Ren m n = Vec (Fin m) n

Subst : Nat → Nat → Set
Subst m n = Vec (Tm m) n

_[_]' : ∀ {m n} → Tm n → Subst m n → Tm m
var i [ ρ ]' = lookup i ρ

sucRen : ∀ {m n} → Ren m n → Ren (suc m) n
sucRen [] = []
sucRen (x ∷ r) = suc x ∷ sucRen r 

idRen : ∀ n → Ren n n
idRen zero = []
idRen (suc n) = zero ∷ sucRen (idRen n)

pRen : ∀ n → Ren (suc n) n
pRen n = sucRen (idRen n)

vrs : ∀ {n m} (r : Ren m n) → Subst m n
vrs [] = []
vrs (x ∷ r) = var x ∷ vrs r

id~ : ∀ n → Subst n n
id~ n = vrs (idRen n)

p~ : ∀ {n}→ Subst (suc n) n
p~ {n} = vrs (pRen n)

_⋆_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
[]       ⋆ σ₂ = []
(α ∷ σ₁) ⋆ σ₂ = α [ σ₂ ]' ∷ σ₁ ⋆ σ₂

varCwf : ∀ {n} (i : Fin n) → Tm-cwf n
varCwf zero    = q
varCwf (suc i) = varCwf i [ p ]

data Fins : Nat → Nat → Set where
  <>    : ∀ {m} → Fins m 0
  <_,_> : ∀ {m n} → Fins m n → Fin m → Fins m (suc n)

sucs : ∀ {m n} → Fins m n → Fins (suc m) n
sucs <> = <>
sucs < is , i > = < (sucs is) , (suc i) >

idFins : ∀ n → Fins n n
idFins zero = <>
idFins (suc n) = < sucs (idFins n) , zero >

pFins : ∀ n → Fins (suc n) n
pFins n = sucs (idFins n)

vars : ∀ {n m} (is : Fins m n) → Hom m n
vars <> = <>
vars < is , i > = < vars is , varCwf i >

pNorm : ∀ n → Hom (suc n) n
pNorm n = vars (pFins n)
