module Unityped.Projection where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin
open import Unityped.UcwfModel

var : ∀ {n} (i : Fin n) → Term n
var zero    = q
var (suc i) = var i [ p _ ]

data Fins : Nat → Nat → Set where
  <> : ∀ {m} → Fins m 0
  <_,_> : ∀ {m n} → Fins m n → Fin m → Fins m (suc n)

sucs : ∀ {m n} → Fins m n → Fins (suc m) n
sucs <> = <>
sucs < is , i > = < (sucs is) , (suc i) >

idFins : ∀ n → Fins n n
idFins zero = <>
idFins (suc n) = < sucs (idFins n) , zero >

pFins : ∀ n → Fins (suc n) n
pFins zero = <>
pFins (suc n) = sucs (idFins (suc n))

vars : ∀ {n m} (is : Fins m n) → Hom m n
vars <> = <>
vars < is , i > = < vars is , var i >

pNorm : ∀ n → Hom (suc n) n
pNorm n = vars (pFins n)

var-lemma : ∀ {m n} (is : Fins m n) → vars is ∘ p m ~ₕ  vars (sucs is)
var-lemma <> = ∘<> (p _)
var-lemma < is , i > = {!!}
