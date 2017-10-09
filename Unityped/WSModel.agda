module Unityped.WSModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec
open import Function renaming (_∘_ to _◯_) using (_$_ ; flip)
open import Relation.Binary using (IsEquivalence ; Setoid)

data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n
  lam : (n : Nat) → WellScopedTm (suc n) → WellScopedTm n
  app : (n : Nat) → WellScopedTm n → WellScopedTm n → WellScopedTm n

1toN_ : ∀ n → Vec (Fin (1 + n)) n
1toN _ = tabulate suc

up : ∀ n → Vec (Fin (2 + n)) n
up _ = tabulate (λ i → suc (suc i))

rename : ∀ {n m} (t : WellScopedTm n) (is : Vec (Fin m) n) → WellScopedTm m
rename {_} {m} (var _ i)   is = var m (lookup i is)
rename {n} {m} (lam _ t)   is = lam m (rename t (zero ∷ map suc is))
rename {n} {m} (app _ t u) is = app m (rename t is) (rename u is)

VecTerm : Nat → Nat → Set
VecTerm n m = Vec (WellScopedTm n) m

-- q
q : (n : Nat) → WellScopedTm (suc n)
q n = var (suc n) zero

-- id
id : (n : Nat) → VecTerm n n
id n = tabulate (var n)

-- weakening (derived)
lift : {n : Nat} → WellScopedTm n → WellScopedTm (suc n)
lift t = rename t (1toN _)

↑ : {n m : Nat} → VecTerm m n → VecTerm (suc m) n
↑ ts = map lift ts

↑² : {n m : Nat} → VecTerm m n → VecTerm (2 + m) n
↑² = ↑ ◯ ↑

-- p
p : (n : Nat) → VecTerm (1 + n) n
p = ↑ ◯ id -- or tabulate (lift ∘ (var n))

-- alternative id and p
id′ : ∀ n → VecTerm n n
id′ n = map (var n) (allFin n)

p′ : (n : Nat) → VecTerm (1 + n) n
p′ n = map (var (1 + n)) (1toN n)

p² : (n : Nat) → VecTerm (2 + n) n
p² n = map (var (2 + n)) (up n)

-- sub
_′[_] : ∀ {n m} → WellScopedTm n → VecTerm m n → WellScopedTm m
_′[_] (var _ i)   ts = lookup i ts
_′[_] (lam _ t)   ts = lam _ (t ′[ q _ ∷ ↑ ts ])
_′[_] (app _ t u) ts = app _ (t ′[ ts ]) (u ′[ ts ])

-- composition of homs 
_∘_ : ∀ {m n k} → VecTerm n k → VecTerm m n → VecTerm m k
_∘_ []        _ = []
_∘_ (t ∷ ts) us = t ′[ us ] ∷ ts ∘ us

_∘₁_ : ∀ {m n k} → VecTerm n k → VecTerm m n → VecTerm m k
_∘₁_ ts us = map (_′[ us ]) ts

_∘₂_ : ∀ {m n k} → VecTerm n k → VecTerm m n → VecTerm m k
_∘₂_ ts us = tabulate (λ i → lookup i ts ′[ us ])

-- < Δ , τ >
ext : ∀ {m n} → VecTerm m n → WellScopedTm m → VecTerm m (1 + n)
ext ts t = t ∷ ts

-- <>
empt : ∀ {m} → VecTerm m 0
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
