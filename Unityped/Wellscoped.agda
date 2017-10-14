{- 

Scope safe untyped lambda calculus terms; the terms are a family of types indexed
by the number of free variables contained in each term. Variables are in 
de Bruijn style, i.e., nameless. 

Substitutions are vectors of terms and substitution is a meta operation.
The formulation is much like the λσ calculus with explicit substitutions (Abadi et al)

-}
module Unityped.Wellscoped where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_])
open import Function as Fun using (_∘_ ; _$_ ; flip)
open import Relation.Binary using (IsEquivalence ; Setoid)

infix 10 _`$_
infix 8 _⊚_
infix 8 _⊙_
infix 8 _⊙r_
infix 8 _r⊙_
infix 7 _∙_
infix 9 _~_

data Term (n : Nat) : Set where
  var   : (ι : Fin n)        → Term n
  `λ    : (t : Term (1 + n)) → Term n
  _`$_  : (t₁ t₂ : Term n)   → Term n

q : (n : Nat) → Term (1 + n)
q n = var zero

Sub : (Nat → Set) → Nat → Nat → Set
Sub T m n = Vec (T m) n

Ren : Nat → Nat → Set
Ren m n = Sub Fin m n

↑_ : ∀ {m n} → Ren m n → Ren (1 + m) (1 + n)
↑_ = λ ρ → zero ∷ map suc ρ

idF : ∀ {n} → Ren n n
idF = allFin _

ren : ∀ {n m} → Term n → Ren m n → Term m
ren (var i)  ρ = var (lookup i ρ)
ren (`λ t)   ρ = `λ (ren t (↑ ρ))
ren (t `$ u) ρ = (ren t ρ) `$ (ren u ρ)

_⊚_ : ∀ {m n k} → Ren m n → Ren k m → Ren k n
ρ₁ ⊚ ρ₂ = map (flip lookup ρ₂) ρ₁

wkR : ∀ m {n} → Ren (m + n) n
wkR zero    = idF
wkR (suc m) = map suc (wkR m) 

pR : ∀ {n} → Ren (1 + n) n
pR = wkR 1

Subst : Nat → Nat → Set
Subst m n = Sub Term m n

_∙_ : ∀ {n m} → Subst m n → Term m → Subst m (1 + n)
σ ∙ t = t ∷ σ

ren2sub : ∀ {m n} → Ren m n → Subst m n
ren2sub = map var

id : ∀ n → Subst n n
id n = tabulate var

weaken : ∀ {m} → Term m → Term (1 + m)
weaken = flip ren pR

↑ₛ_ : ∀ {m n} → Subst m n → Subst (1 + m) (1 + n)
↑ₛ_ = (q _ ∷_) ∘ map weaken 

_[_] : ∀ {m n} → Term n → Subst m n → Term m
var i    [ σ ] = lookup i σ
`λ t     [ σ ] = `λ (t [ ↑ₛ σ ])
(t `$ u) [ σ ] = t [ σ ] `$ u [ σ ]

_⊙_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
σ₁ ⊙ σ₂ = map (_[ σ₂ ]) σ₁

_⊙₂_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
[]       ⊙₂ σ₂ = []
(α ∷ σ₁) ⊙₂ σ₂ = (σ₁ ⊙₂ σ₂) ∙ (α [ σ₂ ])

_r⊙_ : ∀ {m n k} → Ren m n → Subst k m → Subst k n
ρ r⊙ σ = map (flip lookup σ) ρ

_⊙r_ : ∀ {m n k} → Subst m n → Ren k m → Subst k n
σ ⊙r ρ = map (flip ren ρ) σ

1toN_ : ∀ n → Ren (1 + n) n
1toN _ = tabulate suc

p' : ∀ {n} → Subst (1 + n) n
p' = map (λ t → ren t pR) (id _)

p : ∀ n → Subst (1 + n) n
p n = tabulate (var ∘ suc)

weaken' : ∀ {m} → Term m → Term (1 + m)
weaken' t = t [ p _ ]

p′ : ∀ m n → Subst (m + n) n
p′ zero    n = id n
p′ (suc m) n = p′ m n ⊙ p (m + n)

-- β convertability as an inductive relation
data _~_  {n : Nat} : (t u : Term n) → Set where
  varcong : (i : Fin n) → var i ~ var i
  apcong  : (t u t′ u′ : Term n) → t ~ t′ → u ~ u′ → t `$ u ~ t′ `$ u′
  ξ       : (t u : Term (1 + n)) → t ~ u → `λ t ~ `λ u
  β       : (t : Term (1 + n)) (u : Term n) → `λ t `$ u ~ t [ id n ∙ u ]
  η       : (t : Term n) → `λ (weaken t `$ q n) ~ t
  sym~    : {t₁ t₂ : Term n} → t₁ ~ t₂ → t₂ ~ t₁
  trans~  : {t₁ t₂ t₃ : Term n} → t₁ ~ t₂ → t₂ ~ t₃ → t₁ ~ t₃

refl~ : ∀ {n} {t : Term n} → t ~ t
refl~ {n} {t} = trans~ (sym~ (η t)) (η t)

~equiv : ∀ {n} → IsEquivalence (_~_ {n})
~equiv = record { refl  = refl~
                ; sym   = sym~
                ; trans = trans~ }

TermSetoid : ∀ {n} → Setoid _ _
TermSetoid {n} = record { Carrier = Term n
                        ; _≈_ = _~_
                        ; isEquivalence = ~equiv }

