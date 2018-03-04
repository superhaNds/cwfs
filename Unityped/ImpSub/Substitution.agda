-------------------------------------------------------------
-- Substitutions and renaming for the untyped lambda calculus
-- using vectors of a specific length.
-------------------------------------------------------------

module Unityped.ImpSub.Substitution where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Fin.Substitution renaming (Sub to SubF ; Subst to SubstF)
open import Data.Fin.Substitution.Lemmas
open import Data.Vec hiding ([_])
open import Function as F using (_$_ ; flip)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unityped.ImpSub.Syntax
import Unityped.ExpSub.Projection as Pr
open ≡-Reasoning

-------------------------------------------------------------
-- Renamings

infix 8 _⊚_
infix 8 _∘_
infix 8 _∘r_
infix 8 _r∘_
infix 7 _,_

-- A polymorphic substitution

Sub : (Nat → Set) → Nat → Nat → Set
Sub T m n = Vec (T m) n

-- Renaming are substitutions of numbers

Ren : Nat → Nat → Set
Ren m n = Sub Fin m n

-- the lifting substitution for renamings

lift-ren : ∀ {m n} → Ren m n → Ren (1 + m) (1 + n)
lift-ren = λ ρ → zero ∷ map suc ρ

-- The identity substistuion for renamings

idF : ∀ {n} → Ren n n
idF = allFin _

-- The renaming operation on terms

ren : ∀ {n m} → Tm n → Ren m n → Tm m
ren (var i) ρ = var (lookup i ρ)
ren (ƛ t)   ρ = ƛ (ren t (lift-ren ρ))
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
Subst m n = Sub Tm m n

-- Cons to resemble Ucwf syntax

_,_ : ∀ {n m} → Subst m n → Tm m → Subst m (1 + n)
σ , t = t ∷ σ

ren2sub : ∀ {m n} → Ren m n → Subst m n
ren2sub = map var

-- The identity substituion

id : ∀ {n} → Subst n n
id = tabulate var

-- Weakening a term is renaming it in the projection sub for Fin

weaken : ∀ {m} → Tm m → Tm (1 + m)
weaken t = ren t pR

weaken-subst : ∀ {m n} → Subst m n → Subst (1 + m) n
weaken-subst = map weaken

-- The weakening substitution for terms

↑_ : ∀ {m n} → Subst m n → Subst (1 + m) (1 + n)
↑_ = (_, q) F.∘ weaken-subst

-- The substitution operation, which is a meta level operation

_[_] : ∀ {m n} → Tm n → Subst m n → Tm m
var i    [ σ ] = lookup i σ
ƛ t      [ σ ] = ƛ (t [ ↑ σ ])
(t · u)  [ σ ] = t [ σ ] · u [ σ ]

-- Compositions of substitutions

_∘_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
σ₁ ∘ σ₂ = map (_[ σ₂ ]) σ₁

-- Equivalent composition operator as helper

_∘₂_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
[]       ∘₂ σ₂ = []
(α ∷ σ₁) ∘₂ σ₂ = (σ₁ ∘₂ σ₂) , (α [ σ₂ ])

-- Helper operations that relate renamings and substitutions

_r∘_ : ∀ {m n k} → Ren m n → Subst k m → Subst k n
ρ r∘ σ = map (flip lookup σ) ρ

_∘r_ : ∀ {m n k} → Subst m n → Ren k m → Subst k n
σ ∘r ρ = map (flip ren ρ) σ

-- the sequence of fins from 1 to n

1toN_ : ∀ n → Ren (1 + n) n
1toN _ = tabulate suc

-- The projection substitution for terms, expressed in two different ways
-- the second definition is much easier to reason with for many proofs

p' : ∀ {n} → Subst (1 + n) n
p' = map (λ t → ren t pR) id

p : ∀ {n} → Subst (1 + n) n
p = tabulate (λ x → var (suc x))

-- Another version of weakening

weaken' : ∀ {m} → Tm m → Tm (1 + m)
weaken' t = t [ p ]

-- A generalized projection substitution

p′ : ∀ m n → Subst (m + n) n
p′ zero    n = id
p′ (suc m) n = p′ m n ∘ p

-------------------------------------------------------------------------------------------
-- Some utilities for the proving the p lemma for the isomoprhism

open Pr.Fins

mapTT : ∀ {n m} (f : Fin m → Tm m) (is : Fins m n) → Subst m n
mapTT f <>         = []
mapTT f < is , x > = f x ∷ mapTT f is

pp : ∀ n → Subst (suc n) n
pp n = mapTT var (pFins n)

abstract

  lookup-fn-map : ∀ {m n} (i : Fin n) (is : Fins m n) (f : Fin m → Tm m) →
                  lookup i (mapTT f is) ≡ f (lookup-fn i is)
  lookup-fn-map zero    < is , x > f = refl
  lookup-fn-map (suc i) < is , x > f = lookup-fn-map i is f

  lookup-fn-pf : ∀ {n} (i : Fin n) → lookup-fn i (pFins n) ≡ suc i
  lookup-fn-pf i = begin
    lookup-fn i (mapFins (tab (λ z → z)) suc) ≡⟨ cong (lookup-fn i) (sym (tabulate-∘ suc (λ z → z))) ⟩
    lookup-fn i (tab (λ x → suc x))           ≡⟨ lookup∘tab suc i ⟩
    suc i                                     ∎

  lookup-mapTT : ∀ {n} (i : Fin n) → lookup i (mapTT var (pFins n)) ≡ var (suc i)
  lookup-mapTT i = begin
    lookup i (mapTT var (pFins _)) ≡⟨ lookup-fn-map i (pFins _) var ⟩
    var (lookup-fn i (pFins _))    ≡⟨ cong var (lookup-fn-pf i) ⟩
    var (suc i)                    ∎
