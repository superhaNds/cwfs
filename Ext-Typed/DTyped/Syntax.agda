module Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin
open import Data.Vec hiding ([_])

data Tm (n : Nat) : Set where
  var : (i : Fin n) → Tm n
  ƛ   : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n
  Π   : Tm n → Tm (suc n) → Tm n
  U   : Tm n

var₀ : ∀ {n} → Tm (suc n)
var₀ = var zero

Ren : Nat → Nat → Set
Ren m n = Vec (Fin m) n

Subst : Nat → Nat → Set
Subst m n = Vec (Tm m) n

id : ∀ {n} → Subst n n
id = tabulate var

_∙_ : ∀ {m n} → Subst m n → Tm m → Subst m (suc n)
ρ ∙ t = t ∷ ρ

p : ∀ {n} → Subst (suc n) n
p = map var (tabulate suc)

lift-fins : ∀ {m n} → Ren m n → Ren (suc m) (suc n)
lift-fins ρ = zero ∷ (map suc ρ)

ren : ∀ {m n} → Tm n → Ren m n → Tm m
ren (var i) ρ = var (lookup i ρ)
ren (ƛ t)   ρ = ƛ (ren t (lift-fins ρ))
ren (t · u) ρ = (ren t ρ) · (ren u ρ)
ren (Π A B) ρ = Π (ren A ρ) (ren B (lift-fins ρ))
ren U       _ = U

wk : ∀ {n} → Tm n → Tm (suc n)
wk t = ren t (tabulate suc)

wk-subst : ∀ {m n} → Subst m n → Subst (suc m) n
wk-subst = map wk

↑_ : ∀ {m n} (ρ : Subst m n) → Subst (suc m) (suc n)
↑ ρ = wk-subst ρ ∙ var₀

_[_] : ∀ {m n} (t : Tm n) (ρ : Subst m n) → Tm m
var i   [ ρ ] = lookup i ρ
ƛ t     [ ρ ] = ƛ (t [ ↑ ρ ])
(t · u) [ ρ ] = (t [ ρ ]) · (u [ ρ ])
Π A B   [ ρ ] = Π (A [ ρ ]) (B [ ↑ ρ ])
U       [ _ ] = U

_⋆_ : ∀ {m n k} → Subst n k → Subst m n → Subst m k
ρ ⋆ σ = map (_[ σ ]) ρ
