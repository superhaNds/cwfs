{-# OPTIONS --allow-unsolved-metas #-}
module Unityped.WSModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_$_)
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Unityped.Ucwf
open ≡-Reasoning

data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n
  lam : (n : Nat) → WellScopedTm (suc n) → WellScopedTm n
  app : (n : Nat) → WellScopedTm n → WellScopedTm n → WellScopedTm n

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
id : (n : Nat) → Vec (WellScopedTm n) n
id n = tabulate (var n)

-- weakening (derived)
lift : {n : Nat} → WellScopedTm n → WellScopedTm (suc n)
lift t = rename t (↑ _)

-- p
p : (n : Nat) → Vec (WellScopedTm (suc n)) n
p n = map lift (id n) -- or tabulate (lift ∘ (var n))

-- sub
_′[_] : ∀ {n m} → WellScopedTm n → Vec (WellScopedTm m) n → WellScopedTm m
_′[_] (var _ i)   ts = lookup i ts
_′[_] (lam _ t)   ts = lam _ (t ′[ q _ ∷ map lift ts ])
_′[_] (app _ t u) ts = app _ (t ′[ ts ]) (u ′[ ts ])

-- composition of homs 
_∘_ : ∀ {m n k} → Vec (WellScopedTm n) k → Vec (WellScopedTm m) n → Vec (WellScopedTm m) k
_∘_ []        _ = []
_∘_ (t ∷ ts) us = t ′[ us ] ∷ ts ∘ us

-- < Δ , τ >
ext : ∀ {m n} → Vec (WellScopedTm m) n → WellScopedTm m → Vec (WellScopedTm m) (suc n)
ext ts t = t ∷ ts

-- <>
empt : ∀ {m} → Vec (WellScopedTm m) zero
empt = []

-- β convertibility
data _~_ : {n : Nat} (t₁ t₂ : WellScopedTm n) → Set where
  varcong : ∀ {n} (i : Fin n) → var n i ~ var n i
  appcong : ∀ {n} {t t′ u u′ : WellScopedTm n} → t ~ t′ → u ~ u′ → app n t u ~ app n t′ u′
  ξ       : ∀ {n} {t u : WellScopedTm (suc n)} → t ~ u → lam n t ~ lam n u
  β       : ∀ {n} (t : WellScopedTm (suc n)) (u : WellScopedTm n) → app n (lam n t) u ~ (t ′[ u ∷ id n ])
  η       : ∀ {n} (t : WellScopedTm n) → lam n (app (suc n) (lift t) (q n)) ~ t
  sym~    : ∀ {n} {t u : WellScopedTm n} → t ~ u → u ~ t
  trans~  : ∀ {n} {t u v : WellScopedTm n} → t ~ u → u ~ v → t ~ v

refl~ : ∀ {n} {t : WellScopedTm n} → t ~ t
refl~ {_} {t} = trans~ (sym~ $ η t) (η t)

~equiv : ∀ {n} → IsEquivalence (_~_ {n})
~equiv = record { refl = refl~
                ; sym = sym~
                ; trans = trans~ }

WsSetoid : ∀ {n} → Setoid _ _
WsSetoid {n} = record { Carrier = WellScopedTm n
                      ; _≈_ = _~_
                      ; isEquivalence = ~equiv }

-- Proofs 

liftVar : ∀ n i → lift (var n i) ≡ var (suc n) (suc i)
liftVar n i = cong (var (suc n)) (lookup∘tabulate suc i)

lookupIdLemma : ∀ n i → lookup i (id n) ≡ var n i
lookupIdLemma n i = lookup∘tabulate (var n) i

lookupPLemma : ∀ n i → lookup i (p n) ≡ var (suc n) (suc i)
lookupPLemma n i =
  begin
    lookup i (p n)
  ≡⟨⟩
    lookup i (map lift (id n))
  ≡⟨ sym (lookupMap n i (id n)) ⟩
    lift (lookup i (id n))
  ≡⟨ cong lift (lookupIdLemma n i) ⟩
    lift (var n i)
  ≡⟨ liftVar n i ⟩
    var (suc n) (suc i)
  ∎ where lookupMap : ∀ {A B : Set} {f : A → B} (n : Nat) (i : Fin n) (xs : Vec A n)
                        → f (lookup i xs) ≡ lookup i (map f xs)
          lookupMap (suc n) zero    (x ∷ xs) = refl
          lookupMap (suc n) (suc i) (x ∷ xs) = lookupMap n i xs

subVarP : ∀ n i → (var n i) ′[ p n ] ≡ var (suc n) (suc i)
subVarP = lookupPLemma

subLift : ∀ n x → lift x ≡ x ′[ p n ]
subLift n (var _ i)   = trans (liftVar _ i) (sym (subVarP _ i))
subLift n (lam _ t)   = {!!}
subLift n (app _ t u) = trans (cong (λ x → app _ x _) (subLift _ t))
                              (cong (λ x → app _ _ x) (subLift _ u))

lift∘p : ∀ {n m : Nat} (xs : Vec (WellScopedTm n) m) → map lift xs ≡ xs ∘ p n
lift∘p []       = refl
lift∘p (x ∷ xs) = trans (cong (λ s → s ∷ _) (subLift _ x))
                           (cong (λ s → _ ∷ s) (lift∘p xs))
                           
bruh : ∀ n → id n ∘ p n ≡ tail (id (1 + n))
bruh zero = refl
bruh (suc n) =
  begin
    id _ ∘ p _
  ≡⟨⟩
    (q _) ′[ tail $ id (2 + n) ] ∷ (tail $ id _) ∘ p _
  ≡⟨⟩
    var _ (suc zero) ∷ (tail $ id _) ∘ p _
  ≡⟨ {!!} ⟩
    var _ (suc zero) ∷ tail (tail (id (2 + n)))
  ∎

tailIdp : ∀ n → tail (id (suc n)) ≡ p n
tailIdp n = sym $
  begin
    p n
  ≡⟨⟩
    map lift (id n)
  ≡⟨ lift∘p (id n) ⟩
    id n ∘ p n
  ≡⟨ bruh n ⟩ 
    tail (id _)
  ∎

postulate
  tailC : ∀ {n k} (x : WellScopedTm n) (xs : Vec (WellScopedTm n) k)
            → tail (id (1 + k)) ∘ (x ∷ xs) ≡ xs

id=<p,q> : ∀ (n : Nat) → id (suc n) ≡ q n ∷ p n 
id=<p,q> n = cong (_∷_ (q _)) (tailIdp n)

t[id]=t : ∀ {n} → (t : WellScopedTm n) → t ′[ id n ] ≡ t
t[id]=t (var n i) = lookupIdLemma n i
t[id]=t (lam n t) = trans (cong (λ x → lam _ (t ′[ x ])) (sym $ id=<p,q> _))
                          (cong (lam n) (t[id]=t t))
t[id]=t (app n t u) = trans (cong (λ z → app n z (u ′[ id n ])) (t[id]=t t))
                            (cong (app n t) (t[id]=t u))

id0=[] : id 0 ≡ empt
id0=[] = refl

∘-empty : ∀ {m n} (ts : Vec (WellScopedTm m) n) → empt ∘ ts ≡ empt
∘-empty _ = refl

∘-assoc : ∀ {m n k j} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n)
    (vs : Vec (WellScopedTm j) m) → (ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)

compInSub : ∀ {m n k} (t : WellScopedTm n) (ts : Vec (WellScopedTm k) n)
    (us : Vec (WellScopedTm m) k) → t ′[ ts ∘ us ] ≡ t ′[ ts ] ′[ us ]

p∘x∷ts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k) → p k ∘ (t ∷ ts) ≡ ts
p∘x∷ts t ts =
  begin
    p _ ∘ (t ∷ ts)
  ≡⟨ cong (λ x → x ∘ (t ∷ ts)) (sym (tailIdp _)) ⟩
    (tail $ id _) ∘ (t ∷ ts)
  ≡⟨ tailC t ts ⟩ 
    ts
  ∎

compInSub (var _ zero)    (v ∷ ts) us = refl
compInSub (var _ (suc i)) (v ∷ ts) us = compInSub (var _ i) ts us
compInSub (lam n t)       ts       us = sym $
  begin
    _
  ≡⟨ cong (lam _) (sym $ compInSub t (q _ ∷ map lift ts) (q _ ∷ map lift us)) ⟩
    _
  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ∘ _ ])) (lift∘p ts) ⟩
    _
  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ _ ∘ (q _ ∷ x) ])) (lift∘p us) ⟩
    _
  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ])) {!!} ⟩ -- ∘-assoc ts (projSub _) (q _ ∷ comp us (projSub _))
    _
  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ ts ∘ x ])) (p∘x∷ts (q _) (us ∘ p _)) ⟩  -- 
    _
  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ])) (sym {!!}) ⟩ -- ∘-assoc ts us (projSub _)
    _
  ≡⟨ cong (λ x → lam _ (t ′[ q _ ∷ x ])) (sym (lift∘p (ts ∘ us))) ⟩ 
    _
  ∎
compInSub (app n t u) ts us =
  trans (cong (λ z → app _ z (u ′[ ts ∘ us ])) (compInSub t ts us))
        (cong (app _ (t ′[ ts ] ′[ us ])) (compInSub u ts us))

tailComp : ∀ n → (p n) ∘ (p (1 + n)) ≡ tail (p (1 + n))
tailComp n = p∘x∷ts _ (tail (p (suc n)))

∘-lid : ∀ {m n : Nat} (ts : Vec (WellScopedTm m) n) → id n ∘ ts ≡ ts
∘-lid [] = refl
∘-lid (x ∷ ts) =
  trans (cong (λ a → (q _ ′[ x ∷ ts ]) ∷ a ∘ (x ∷ ts)) (tailIdp _))
        (cong (λ a → (q _ ′[ x ∷ ts ]) ∷ a) (p∘x∷ts x ts))

∘-rid : ∀ {m n : Nat} (ts : Vec (WellScopedTm m) n) → ts ∘ id m  ≡ ts
∘-rid [] = refl
∘-rid (x ∷ ts) rewrite t[id]=t x
                           | ∘-rid ts = refl

∘-assoc []       us vs = refl
∘-assoc (x ∷ ts) us vs = sym $
  trans (cong (λ d → d ∷ ts ∘ (us ∘ vs)) (compInSub x us vs))
        (sym (cong (_∷_ (x ′[ us ] ′[ vs ])) (∘-assoc ts us vs)))

wsTermsAsUcwf : Ucwf (WellScopedTm)
wsTermsAsUcwf = record
                  { id       = id
                  ; <>       = empt
                  ; p        = p
                  ; q        = q
                  ; _∘_      = _∘_
                  ; _[_]     = _′[_]
                  ; <_,_>    = ext
                  ; id₀      = id0=[]
                  ; ∘<>      = ∘-empty
                  ; id<p,q>  = id=<p,q> _
                  ; ∘lid     = ∘-lid
                  ; ∘rid     = ∘-rid
                  ; ∘asso    = ∘-assoc
                  ; subid    = t[id]=t
                  ; p∘<γ,α>  = p∘x∷ts
                  ; q[<γ,α>] = λ _ _ → refl
                  ; ∘inSub   = compInSub
                  ; <δ,α>∘γ  = λ _ _ _ → refl
                  }

