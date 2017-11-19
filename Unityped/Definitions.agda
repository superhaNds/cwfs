module Definitions where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Data.Vec hiding ([_])
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_])


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
         
cong-≡ : ∀ {m n} {A : Set} {t u} (f : A → Hom m n) → t ≡ u → f t ~~ f u
cong-≡ f refl = refl~~

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

lookup-fn : ∀ {m n} → Fin n → Fins m n → Fin m
lookup-fn zero < is , x > = x
lookup-fn (suc i) < is , x > = lookup-fn i is

tab : ∀ {n m} → (Fin n → Fin m) → Fins m n
tab {zero} f = <>
tab {suc n} f = < (tab (λ x → f (suc x))) , (f zero) >

idFins' : ∀ {n} → Fins n n
idFins' = tab (λ x → x)

lookup∘tab : ∀ {m n} (f : Fin n → Fin m) (i : Fin n) →
                  lookup-fn i (tab f) ≡ f i
lookup∘tab f zero = refl
lookup∘tab f (suc i) = lookup∘tab (λ z → f (suc z)) i





ren2fins : ∀ {m n} → Ren m n → Fins m n
ren2fins [] = <>
ren2fins (x ∷ ρ) = < ren2fins ρ , x >

fins2ren : ∀ {m n} → Fins m n → Ren m n
fins2ren <> = []
fins2ren < is , x > = x ∷ fins2ren is

fins~ren : ∀ {m n} (is : Fins m n) → ren2fins (fins2ren is) ≡ is
fins~ren <> = refl
fins~ren < is , x > = cong (λ z → < z , x >) (fins~ren is)

ren~fins : ∀ {m n} (ρ : Ren m n) → fins2ren (ren2fins ρ) ≡ ρ
ren~fins [] = refl
ren~fins (x ∷ ρ) = cong (_∷_ x) (ren~fins ρ)


mapFins : ∀ {n m k} (is : Fins m n) (f : Fin m → Fin k) → Fins k n
mapFins <> f = <>
mapFins < is , x > f = < mapFins is f , f x >

sucs : ∀ {m n} → Fins m n → Fins (suc m) n
sucs is = mapFins is suc

idFins : ∀ n → Fins n n
idFins n = tab (λ x → x)
{-
idFins zero = <>
idFins (suc n) = < sucs (idFins n) , zero >

-}

pFins : ∀ n → Fins (suc n) n
pFins n = sucs (idFins n)

vars : ∀ {n m} (is : Fins m n) → Hom m n
vars <> = <>
vars < is , i > = < vars is , varCwf i >

pNorm : ∀ n → Hom (suc n) n
pNorm n = vars (pFins n)


mapT : ∀ {n m} (f : Fin m → Tm-cwf m) (is : Fins m n) → Hom m n
mapT f <> = <>
mapT f < is , x > = < mapT f is , f x >

mapTT : ∀ {n m} (f : Fin m → Tm m) (is : Fins m n) → Subst m n
mapTT f <> = []
mapTT f < is , x > = f x ∷ mapTT f is

mapV : ∀ {n m k} (ρ : Ren m n) (f : Fin m → Fin k) → Ren k n
mapV [] f = []
mapV (x ∷ ρ) f = f x ∷ mapV ρ f

pn' : ∀ n → Hom (suc n) n
pn' n = vars (mapFins (idFins n) suc)

kkk : ∀ {m n} (is : Ren m n) → ren2fins (sucRen is) ≡ sucs (ren2fins is)
kkk [] = refl
kkk (x ∷ is) = cong (λ z → < z , suc x >) (kkk is)

tvars : ∀ {m n} → Fins m n → Subst m n
tvars <> = []
tvars < is , x > = (var x) ∷ tvars is

pp : ∀ n → Subst (suc n) n
pp n = mapTT var (pFins n)


tabulate-∘ : ∀ {n m k}
             (f : Fin m → Fin k) (g : Fin n → Fin m) →
             tab (λ x → f (g x)) ≡ mapFins (tab g) f
tabulate-∘ {zero} f g = refl
tabulate-∘ {suc n} f g = cong (<_, f (g zero) >) (tabulate-∘ f (λ z → g (suc z)))

`p : ∀ n → Subst (suc n) n
`p n = tvars (pFins n)

