------------------------------------------------------
-- Scope safe lambda calculus terms using de Bruijn
-- variables. The terms form a family of types indexed
-- by the number of free variables in a given term
------------------------------------------------------

module Unityped.Wellscoped.Syntax where

open import Data.Nat renaming (ℕ to Nat)
import Data.Vec as Vec
open import Data.Fin hiding (_≤?_ ; _+_)
open import Relation.Nullary.Decidable

------------------------------------------------------
-- Term syntax

infix 10 _·_

data Term (n : Nat) : Set where
  var  : (i : Fin n)    → Term n
  _·_  : (t u : Term n) → Term n
  ƛ    : (t : Term (1 + n)) → Term n

vr : ∀ m {n} {m<n : True (suc m ≤? n)} → Term n
vr _ {m<n = m<n} = var (#_ _ {m<n = m<n})

-- The variable with de Bruijn index zero

q : {n : Nat} → Term (1 + n)
q = vr 0

------------------------------------------------------
-- Examples

-- The identity combinator λx.x

I : Term 0
I = ƛ q

-- The K combinator λxy.x

K : Term 0
K = ƛ (ƛ (vr 1))

-- A non terminating term, i.e., the omega combinator

Ω : Term 0
Ω = ω · ω
  where ω : Term 0
        ω = ƛ (q · q)

------------------------------------------------------
-- Type system

infixr 8 _⇒_

data Ty : Set where
  nat : Ty
  _⇒_ : (σ τ : Ty) → Ty

Ctx : Nat → Set
Ctx = Vec.Vec Ty

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctx n) : Term n → Ty → Set where
  var : ∀ {i} → Γ ⊢ var i ∈ Vec.lookup i Γ
  ƛ   : ∀ {t σ τ} (t∈ : σ Vec.∷ Γ ⊢ t ∈ τ) → Γ ⊢ ƛ t ∈ σ ⇒ τ
  _·_ : ∀ {t₁ t₂ σ τ} (t₁∈ : Γ ⊢ t₁ ∈ σ ⇒ τ) (t₂∈ : Γ ⊢ t₂ ∈ σ) →
        Γ ⊢ t₁ · t₂ ∈ τ
