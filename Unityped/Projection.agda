module Unityped.Projection where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin
import Relation.Binary.EqReasoning as EqR
open import Unityped.UcwfModel

var : ∀ {n} (i : Fin n) → Term n
var zero    = q
var (suc i) = var i [ p _ ]

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

var-lemma : ∀ {m n} (is : Fins m n) → vars is ∘ p m ~ₕ vars (sucs is)
var-lemma <> = ∘<> (p _)
var-lemma < is , i > = begin
  < vars is , var i > ∘ p _          ≈⟨ maps (var i) (vars is) (p _) ⟩
  < vars is ∘ p _ , var i [ p _ ] >  ≈⟨ cong~ₕ (<_, var i [ p _ ] >) (var-lemma is) ⟩
  < vars (sucs is) , var (suc i) >   ≈⟨ refl~ₕ ⟩
  vars (sucs < is , i > )            ∎
  where open EqR (HomS {_} {_})

p~vars : ∀ n → p n ~ₕ pNorm n
p~vars zero = hom0~<> (p 0)
p~vars (suc n) = begin
  p (suc n)                                           ≈⟨ eta (p (suc n)) ⟩
  < p n ∘ p (suc n) , q [ p (suc n) ] >               ≈⟨ cong~ₕ (λ x → < x ∘ p (suc n) , q [ p _ ] >) (p~vars n) ⟩
  < vars (pFins n) ∘ p (suc n) , q [ p (suc n) ] >    ≈⟨ cong~ₕ (<_, q [ p _ ] >) (var-lemma (sucs (idFins n))) ⟩
  < vars (sucs (pFins n)) , q [ p (suc n) ] >         ≈⟨ refl~ₕ ⟩
  < vars (sucs (sucs (idFins n))) , q [ p (suc n) ] > ∎
  where open EqR (HomS {_} {_})

{-

<
< < <> , ((q `[ p 1 ]) `[ p 2 ]) `[ p 3 ] > , (q `[ p 2 ]) `[ p 3 ]
>
, q `[ p 3 ] >

< < < <> , ((q [ p 1 ]) [ p 2 ]) [ p 3 ] > , (q [ p 2 ]) [ p 3 ] >
, q [ p 3 ] >

-}
