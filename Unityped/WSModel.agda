{-# OPTIONS --allow-unsolved-metas #-}
module Unityped.WSModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec.Properties
open import Data.Vec
  using (Vec ; [] ; _∷_ ; map ; lookup ; allFin ; tabulate ; tail ; head)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_ ; _$_)
open import Relation.Binary.PropositionalEquality
open import Unityped.Ucwf
open ≡-Reasoning

data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n
  lam : (n : Nat) → WellScopedTm (suc n) → WellScopedTm n
  app : (n : Nat) → WellScopedTm n → WellScopedTm n → WellScopedTm n

id : (n : Nat) → Vec (Fin n) n
id = allFin

↑_ : ∀ n → Vec (Fin (suc n)) n
↑ _ = tabulate suc

rename : ∀ {n m} (t : WellScopedTm n) (is : Vec (Fin m) n) → WellScopedTm m
rename {_} {m} (var _ i)   is = var m (lookup i is)
rename {n} {m} (lam _ t)   is = lam m (rename t (zero ∷ map suc is))
rename {n} {m} (app _ t u) is = app m (rename t is) (rename u is)

-- q
q : (n : Nat) → WellScopedTm (suc n)
q n = var (suc n) zero

-- id
idSub : (n : Nat) → Vec (WellScopedTm n) n
idSub n = tabulate (var n)

-- weakening (derived)
lift : {n : Nat} → WellScopedTm n → WellScopedTm (suc n)
lift t = rename t (↑ _)

-- p
projSub : (n : Nat) → Vec (WellScopedTm (suc n)) n
projSub = map lift ∘ idSub -- or tabulate (lift ∘ (var n))

-- sub
sub : ∀ {n m} → WellScopedTm n → Vec (WellScopedTm m) n → WellScopedTm m
sub (var _ i)   ts = lookup i ts
sub (lam _ t)   ts = lam _ (sub t (var _ zero ∷ map lift ts))
sub (app _ t u) ts = app _ (sub t ts) (sub u ts)

-- composition of homs 
comp : ∀ {m n k} → Vec (WellScopedTm n) k → Vec (WellScopedTm m) n → Vec (WellScopedTm m) k
comp []   _ = []
comp (t ∷ ts) us = sub t us ∷ comp ts us

-- < Δ , τ >
ext : ∀ {m n} → Vec (WellScopedTm m) n → WellScopedTm m → Vec (WellScopedTm m) (suc n)
ext ts t = t ∷ ts

-- <>
empt : ∀ {m} → Vec (WellScopedTm m) zero
empt = []

-- Proofs 

liftVar : ∀ n i → lift (var n i) ≡ var (suc n) (suc i)
liftVar n i = cong (var (suc n)) (lookup∘tabulate suc i)

lookupIdLemma : ∀ n i → lookup i (idSub n) ≡ var n i
lookupIdLemma n i = lookup∘tabulate (var n) i

lookupPLemma : ∀ n i → lookup i (projSub n) ≡ var (suc n) (suc i)
lookupPLemma n i =
  begin
    lookup i (projSub n)
  ≡⟨⟩
    lookup i (map lift (idSub n))
  ≡⟨ sym (lookupMap n i (idSub n)) ⟩
    lift (lookup i (idSub n))
  ≡⟨ cong lift (lookupIdLemma n i) ⟩
    lift (var n i)
  ≡⟨ liftVar n i ⟩
    var (suc n) (suc i)
  ∎ where lookupMap : ∀ {A B : Set} {f : A → B} (n : Nat) (i : Fin n) (xs : Vec A n)
                        → f (lookup i xs) ≡ lookup i (map f xs)
          lookupMap (suc n) zero    (x ∷ xs) = refl
          lookupMap (suc n) (suc i) (x ∷ xs) = lookupMap n i xs

subVarP : ∀ n i → sub (var n i) (projSub n) ≡ var (suc n) (suc i)
subVarP = lookupPLemma

subLift : ∀ n x → lift x ≡ sub x (projSub n)
subLift n (var _ i)   = trans (liftVar _ i) (sym (subVarP _ i))
subLift n (lam _ t)   = {!!}
subLift n (app _ t u) = trans (cong (λ x → app _ x _) (subLift _ t))
                              (cong (λ x → app _ _ x) (subLift _ u))

liftCompP : ∀ {n m : Nat} (xs : Vec (WellScopedTm n) m) → map lift xs ≡ comp xs (projSub n)
liftCompP []       = refl
liftCompP (x ∷ xs) = trans (cong (λ s → s ∷ _) (subLift _ x))
                           (cong (λ s → _ ∷ s) (liftCompP xs))

postulate tailIdp : ∀ n → tail (idSub (suc n)) ≡ projSub n

id=<p,q> : ∀ (n : Nat) → idSub (suc n) ≡ q n ∷ (projSub n)
id=<p,q> n = cong (_∷_ (q _)) (tailIdp n)

t[id]=t : ∀ {n} → (t : WellScopedTm n) → sub t (idSub n) ≡ t
t[id]=t (var n i) = lookupIdLemma n i
t[id]=t (lam n t) = trans (cong (λ x → lam _ (sub t x)) (sym $ id=<p,q> _))
                          (cong (lam n) (t[id]=t t))
t[id]=t (app n t u) = trans (cong (λ z → app n z (sub u _)) (t[id]=t t))
                            (cong (app n t) (t[id]=t u))

id0=[] : idSub zero ≡ empt
id0=[] = refl

compEmpty : ∀ {m n} (ts : Vec (WellScopedTm m) n) → comp empt ts ≡ empt
compEmpty _ = refl

compAssoc : ∀ {m n k p} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n)
    (vs : Vec (WellScopedTm p) m) → comp (comp ts us) vs ≡ comp ts (comp us vs)

compasp : ∀ {m n k} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m)(suc n))
  → comp (comp ts (projSub n)) us ≡ comp ts (comp (projSub n) us)
compasp [] us = refl
compasp (x ∷ ts) us = {!!}

compInSub : ∀ {m n k} (t : WellScopedTm n) (ts : Vec (WellScopedTm k) n)
    (us : Vec (WellScopedTm m) k) → sub t (comp ts us) ≡ sub (sub t ts) us

subVar0 : ∀ {m n} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) m) →
               sub (q m) (ext ts t) ≡ t
subVar0 t ts = refl

postulate p∘x∷ts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k) → comp (projSub k) (t ∷ ts) ≡ ts

p∘<ts,t>=ts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k)
                → comp (projSub k) (t ∷ ts) ≡ ts
p∘<ts,t>=ts t [] = refl
p∘<ts,t>=ts t (x ∷ xs) = {!!}

{-begin
    comp (projSub _) (t ∷ x ∷ xs)
  ≡⟨⟩
    x ∷ comp (tail (projSub (suc _))) (t ∷ x ∷ xs)
  ≡⟨ cong (λ s → x ∷ comp s (t ∷ x ∷ xs)) (sym (p∘<ts,t>=ts _ (tail (projSub _)))) ⟩
    x ∷ comp (comp (projSub _) (projSub (1 + _))) (t ∷ x ∷ xs)
  ≡⟨ {!!} ⟩
    x ∷ xs
  ∎-}

compInSub (var _ zero)    (v ∷ ts) us = refl
compInSub (var _ (suc x)) (v ∷ ts) us = compInSub (var _ x) ts us
compInSub (lam n t)       ts       us = sym $
  begin
    lam _ (sub (sub t (q _ ∷ map lift ts)) (q _ ∷ map lift us))
  ≡⟨ cong (lam _) (sym $ compInSub t (q _ ∷ map lift ts) (q _ ∷ map lift us)) ⟩
    lam _ (sub t $ q _ ∷ comp (map lift ts) (q _ ∷ map lift us))
  ≡⟨ cong (λ x → lam _ (sub t $ q _ ∷ comp x _)) (liftCompP ts) ⟩
    lam _ (sub t $ q _ ∷ comp (comp ts (projSub _)) (q _ ∷ map lift us))
  ≡⟨ cong (λ x → lam _ (sub t $ q _ ∷ comp _ (q _ ∷ x))) (liftCompP us) ⟩
    lam _ (sub t $ q _ ∷ comp (comp ts (projSub _)) (q _ ∷ comp us (projSub _)))
  ≡⟨ cong (λ x → lam _ (sub t $ q _ ∷ x )) {!!} ⟩  -- compAssoc ts (projSub _) (q _ ∷ comp us (projSub _))
    lam _ (sub t $ q _ ∷ comp ts (comp (projSub _) (q _ ∷ comp us (projSub _))))
  ≡⟨ cong (λ x → lam _ (sub t $ q _ ∷ comp ts x)) (p∘<ts,t>=ts (q _) (comp us (projSub _))) ⟩  -- 
    lam _ (sub t $ q _ ∷ comp ts (comp us (projSub _)))
  ≡⟨ cong (λ x → lam _ (sub t $ q _ ∷ x)) (sym {!!}) ⟩  -- compAssoc ts us (projSub _)
    lam _ (sub t $ q _ ∷ comp (comp ts us) (projSub _))
  ≡⟨ cong (λ x → lam _ (sub t $ q _ ∷ x)) (sym (liftCompP (comp ts us))) ⟩ 
    lam _ (sub t $ q _ ∷ map lift (comp ts us))
  ∎
compInSub (app n t u) ts us =
  trans (cong (λ z → app _ z (sub u (comp ts us))) (compInSub t ts us))
        (cong (app _ (sub (sub t ts) us)) (compInSub u ts us))

tailComp : ∀ n → comp (projSub n) (projSub (1 + n)) ≡ tail (projSub (1 + n))
tailComp n = p∘<ts,t>=ts _ (tail (projSub (suc n)))

compRightOfHomExt : ∀ {m n} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) m)
   (us : Vec (WellScopedTm m) n) → comp (ext ts t) us ≡ ext (comp ts us) (sub t us)
compRightOfHomExt _ _ _ = refl

compLeftId : ∀ {m n : Nat} (ts : Vec (WellScopedTm m) n) → comp (idSub n) ts ≡ ts
compLeftId [] = refl
compLeftId (x ∷ ts) =
  trans (cong (λ a → (sub (q _) (x ∷ ts)) ∷ comp a (x ∷ ts)) (tailIdp _))
        (cong (λ a → (sub (q _) (x ∷ ts)) ∷ a) (p∘x∷ts x ts))

compRightId : ∀ {m n : Nat} (ts : Vec (WellScopedTm m) n) → comp ts (idSub m)  ≡ ts
compRightId [] = refl
compRightId (x ∷ ts) rewrite t[id]=t x
                           | compRightId ts = refl

compAssoc []       us vs = refl
compAssoc (x ∷ ts) us vs = sym $
  trans (cong (λ d → d ∷ comp ts (comp us vs)) (compInSub x us vs))
        (sym (cong (_∷_ (sub (sub x us) vs)) (compAssoc ts us vs)))

wsTermsAsUcwf : Ucwf (WellScopedTm)
wsTermsAsUcwf = record
                  { id       = idSub
                  ; <>       = empt
                  ; p        = projSub
                  ; q        = q
                  ; _∘_      = comp
                  ; _[_]     = sub
                  ; <_,_>    = ext
                  ; id₀      = id0=[]
                  ; ∘<>      = compEmpty
                  ; id<p,q>  = id=<p,q> _
                  ; ∘lid     = compLeftId
                  ; ∘rid     = compRightId
                  ; ∘asso    = compAssoc
                  ; subid    = t[id]=t
                  ; p∘<γ,α>  = p∘x∷ts
                  ; q[<γ,α>] = subVar0
                  ; ∘inSub   = compInSub
                  ; <δ,α>∘γ  = compRightOfHomExt
                  }



ex : ∀ {m n k} (ts : Vec (WellScopedTm (n)) k) (us : Vec (WellScopedTm (m)) ?)
  → comp (map lift ts) (map lift us) ≡ map lift (comp ts us)
ex ts us = ?
