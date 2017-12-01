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
I = ƛ (var zero)

-- The K combinator λxy.x

K : Term 0
K = ƛ (ƛ (vr 1))

-- A non terminating term, i.e., the omega combinator

Ω : Term 0
Ω = ω · ω
  where ω : Term 0
        ω = ƛ (q · q)
        
