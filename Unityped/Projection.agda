module Unityped.Projection where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin
import Relation.Binary.EqReasoning as EqR
open import Unityped.UcwfModel

var : ∀ {n} (i : Fin n) → Term n
var zero    = q
var (suc i) = var i [ p ]

data Fins : Nat → Nat → Set where
  <>    : ∀ {m} → Fins m 0
  <_,_> : ∀ {m n} → Fins m n → Fin m → Fins m (suc n)

sucs : ∀ {m n} → Fins m n → Fins (suc m) n
sucs <> = <>
sucs < is , i > = < (sucs is) , (suc i) >

idFins : ∀ n → Fins n n
idFins zero = <>
idFins (suc n) = < sucs (idFins n) , zero >

pFins : ∀ n → Fins (suc n) n
pFins n = sucs (idFins n)

vars : ∀ {n m} (is : Fins m n) → Hom m n
vars <> = <>
vars < is , i > = < vars is , var i >

pNorm : ∀ n → Hom (suc n) n
pNorm n = vars (pFins n)

var-lemma : ∀ {m n} (is : Fins m n) → vars is ∘ p ~ₕ vars (sucs is)
var-lemma <> = ∘<> p
var-lemma < is , i > = begin
  < vars is , var i > ∘ p           ≈⟨ maps (var i) (vars is) p ⟩
  < vars is ∘ p , var i [ p ] >     ≈⟨ cong~ₕ (<_, var i [ p ] >) (var-lemma is) ⟩
  < vars (sucs is) , var (suc i) >  ≈⟨ refl~ₕ ⟩
  vars (sucs < is , i > )           ∎
  where open EqR (HomS {_} {_})

p~vars : ∀ n → p ~ₕ pNorm n
p~vars zero = hom0~<> (p {0})
p~vars (suc n) = begin
  p                                           ≈⟨ eta p ⟩
  < p ∘ p , q [ p ] >                         ≈⟨ cong~ₕ (λ x → < x ∘ p , q [ p ] >) (p~vars n) ⟩
  < vars (pFins n) ∘ p , q [ p ] >            ≈⟨ cong~ₕ (<_, q [ p ] >) (var-lemma (sucs (idFins n))) ⟩
  < vars (sucs (pFins n)) , q [ p ] >         ≈⟨ refl~ₕ ⟩
  < vars (sucs (sucs (idFins n))) , q [ p ] > ∎
  where open EqR (HomS {_} {_})
