-------------------------------------------------------------
-- Substitutions and renaming for the untyped lambda calculus
-- using vectors of a specific length.
-------------------------------------------------------------

module Unityped.Wellscoped.Substitution where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Fin.Substitution renaming (Sub to SubF ; Subst to SubstF)
open import Data.Fin.Substitution.Lemmas
open import Data.Vec hiding ([_])
open import Function as Fun using (_∘_ ; _$_ ; flip)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Star using (Star; ε; _◅_)
open import Unityped.Wellscoped.Syntax
open ≡-Reasoning

-------------------------------------------------------------
-- Renamings

infix 8 _⊚_
infix 8 _⋆_
infix 8 _⋆r_
infix 8 _r⋆_
infix 7 _∙_

-- A polymorphic substitution

Sub : (Nat → Set) → Nat → Nat → Set
Sub T m n = Vec (T m) n

-- Renaming are substitutions of numbers

Ren : Nat → Nat → Set
Ren m n = Sub Fin m n

-- the lifting substitution for renamings

↑_ : ∀ {m n} → Ren m n → Ren (1 + m) (1 + n)
↑_ = λ ρ → zero ∷ map suc ρ

-- The identity substistuion for renamings

idF : ∀ {n} → Ren n n
idF = allFin _

-- The renaming operation on terms

ren : ∀ {n m} → Term n → Ren m n → Term m
ren (var i) ρ = var (lookup i ρ)
ren (ƛ t)   ρ = ƛ (ren t (↑ ρ))
ren (t · u) ρ = (ren t ρ) · (ren u ρ)

-- Compositions of renamings

_⊚_ : ∀ {m n k} → Ren m n → Ren k m → Ren k n
ρ₁ ⊚ ρ₂ = map (flip lookup ρ₂) ρ₁

-- Weakening renamings

wkR : ∀ m {n} → Ren (m + n) n
wkR zero    = idF
wkR (suc m) = map suc (wkR m) 

pR : ∀ {n} → Ren (1 + n) n
pR = wkR 1

-------------------------------------------------------------
-- The parallel substitutions of terms (vectors of terms)

Subst : Nat → Nat → Set
Subst m n = Sub Term m n

-- Cons to resemble Ucwf syntax

_∙_ : ∀ {n m} → Subst m n → Term m → Subst m (1 + n)
σ ∙ t = t ∷ σ

ren2sub : ∀ {m n} → Ren m n → Subst m n
ren2sub = map var

-- The identity substituion

id : ∀ {n} → Subst n n
id = tabulate var

-- Weakening a term is renaming it in the projection sub for Fin

weakenₛ : ∀ {m} → Term m → Term (1 + m)
weakenₛ = flip ren pR

-- The weakening substitution for terms

↑ₛ_ : ∀ {m n} → Subst m n → Subst (1 + m) (1 + n)
↑ₛ_ = (q ∷_) ∘ map weakenₛ 

-- The substitution operation, which is a meta-operation and not
-- explicit as in the λσ calculus (Abadi et al)

_[_] : ∀ {m n} → Term n → Subst m n → Term m
var i    [ σ ] = lookup i σ
ƛ t      [ σ ] = ƛ (t [ ↑ₛ σ ])
(t · u)  [ σ ] = t [ σ ] · u [ σ ]

-- Compositions of substitutions

_⋆_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
σ₁ ⋆ σ₂ = map (_[ σ₂ ]) σ₁

-- Equivalent composition operator as helper

_⋆₂_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
[]       ⋆₂ σ₂ = []
(α ∷ σ₁) ⋆₂ σ₂ = (σ₁ ⋆₂ σ₂) ∙ (α [ σ₂ ])

-- Helper operations that relate renamings and substitutions

_r⋆_ : ∀ {m n k} → Ren m n → Subst k m → Subst k n
ρ r⋆ σ = map (flip lookup σ) ρ

_⋆r_ : ∀ {m n k} → Subst m n → Ren k m → Subst k n
σ ⋆r ρ = map (flip ren ρ) σ

1toN_ : ∀ n → Ren (1 + n) n
1toN _ = tabulate suc

-- The projection substitution for terms, expressed in two different ways
-- the second definition is much easier to reasoin with for many proofs

p' : ∀ {n} → Subst (1 + n) n
p' = map (λ t → ren t pR) id

p : ∀ {n} → Subst (1 + n) n
p = tabulate (λ x → var (suc x))

idFin : ∀ n → Ren n n
idFin zero = []
idFin (suc n) = zero ∷ map suc (idFin n)

sfins : ∀ {m n} → Ren m n → Ren (suc m) n
sfins [] = []
sfins (i ∷ ρ) = suc i ∷ sfins ρ

pFn : ∀ n → Ren (suc n) n
pFn n = sfins (idFin n)

pp : ∀ n → Subst (1 + n) n
pp n = map var (pFn n)

-- Another version of weakening

weaken' : ∀ {m} → Term m → Term (1 + m)
weaken' t = t [ p ]

-- A generalized projection substitution

p′ : ∀ m n → Subst (m + n) n
p′ zero    n = id
p′ (suc m) n = p′ m n ⋆ p
