------------------------------------------------------
-- Scope safe lambda calculus terms using de Bruijn
-- variables. The terms form a family of types indexed
-- by the number of free variables in a given term
------------------------------------------------------

module ExtSimpTyped.Syntax where

open import Data.Nat renaming (ℕ to Nat)
import Data.Vec as Vec
open import Data.Fin hiding (_≤?_ ; _+_)
open import Relation.Nullary.Decidable

------------------------------------------------------
-- Term syntax

infix 10 _·_

data Tm (n : Nat) : Set where
  var  : (i : Fin n) → Tm n
  _·_  : (t u : Tm n) → Tm n
  ƛ    : (t : Tm (1 + n)) → Tm n

vr : ∀ m {n} {m<n : True (suc m ≤? n)} → Tm n
vr _ {m<n = m<n} = var (#_ _ {m<n = m<n})

-- The variable with de Bruijn index zero

q : {n : Nat} → Tm (1 + n)
q = vr 0

------------------------------------------------------
-- Examples

-- The identity combinator λx.x

I : Tm 0
I = ƛ (var zero)

-- The K combinator λxy.x

K : Tm 0
K = ƛ (ƛ (vr 1))

-- A non terminating term, i.e., the omega combinator

Ω : Tm 0
Ω = ω · ω
  where ω : Tm 0
        ω = ƛ (q · q)
        
