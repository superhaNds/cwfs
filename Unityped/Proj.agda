module Proj where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Data.Vec hiding ([_])
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open import Definitions

-----------------------------------------------------
-- Peter's proof that the 'normalized' version of p is indeed p

-- ≈ = "\eq4"
var-lemma : ∀ {m n} (is : Fins m n) → vars is ∘ p ~~ vars (sucs is)
var-lemma <> = ∘<> p
var-lemma < is , i > = begin
  < vars is , varCwf i > ∘ p           ≈⟨ maps (varCwf i) (vars is) p ⟩
  < vars is ∘ p , varCwf i [ p ] >     ≈⟨ cong-<,> refl~ (var-lemma is) ⟩
  < vars (sucs is) , varCwf (suc i) >  ≈⟨ refl~~ ⟩
  vars (sucs < is , i > )           ∎
  where open EqR (HomS {_} {_})


--- pNorm = vars (pFins n)
-- defined in Definitions.agda

p~vars : ∀ n → p ~~ pNorm n
p~vars zero = hom-0~<> (p {0})
p~vars (suc n) = begin
  p                                           ≈⟨ surj-<,> p ⟩
  < p ∘ p , q [ p ] >                         ≈⟨ cong-<,> refl~ (cong-∘ (p~vars n) (refl~~)) ⟩
  < vars (pFins n) ∘ p , q [ p ] >            ≈⟨ cong-<,> refl~ (var-lemma (sucs (idFins n))) ⟩
  < vars (sucs (pFins n)) , q [ p ] >         ≈⟨ refl~~ ⟩
  < vars (sucs (sucs (idFins n))) , q [ p ] > ∎
  where open EqR (HomS {_} {_})

----------------------------------------------------------------------
-- inverses

⟦_⟧ : ∀ {n} → Tm n → Tm-cwf n
⟦_⟧' : ∀ {n m} → Subst m n → Hom m n

∥_∥ : ∀ {n} → Tm-cwf n → Tm n
∥_∥' : ∀ {m n} → Hom m n → Subst m n


-- vars <> = <>
-- vars < is , i > = < vars is , varCwf i >
⟦ [] ⟧' = <>
⟦ t ∷ ts ⟧' = < ⟦ ts ⟧' , ⟦ t ⟧ > -- since x is always a var in p it's varCwf i
⟦ var i ⟧ = varCwf i


-- ∥ = "\||"
∥ q ∥ = var zero
∥ t [ ts ] ∥ = ∥ t ∥ [ ∥ ts ∥' ]'

∥ id ∥'        = id~ _
∥ h ∘ g ∥'     = ∥ h ∥' ⋆ ∥ g ∥'
∥ p ∥'         = p~
∥ <> ∥'        = []
∥ < h , t > ∥' = ∥ t ∥ ∷ ∥ h ∥'


-- I build p~ on the wellscoped side, exactly like Peter did for the cwf side.
-- The situation is now much clearer than it was with the standard library functions
-- albeit, I still cannot do it...

-- Mirroring the other proof doesnt really work out correctly for me
-- there should be a more primitive build up of some lemmas maybe...

lemmaFins : ∀ n → ⟦ vrs (pRen n) ⟧' ∘ p ~~ ⟦ vrs (sucRen (pRen n)) ⟧'
lemmaFins zero = ∘<> p
lemmaFins (suc n) = begin
  < ⟦ vrs (sucRen (pRen n)) ⟧' , q [ p ] > ∘ p         ≈⟨ maps (q [ p ]) _ p ⟩
  < ⟦ vrs (sucRen (pRen n)) ⟧' ∘ p , q [ p ] [ p ] >   ≈⟨ {!!} ⟩
  < (⟦ vrs (pRen n) ⟧' ∘ p) ∘ p , q [ p ] [ p ] >      ≈⟨ {!!} ⟩
  {!!}                                                 ∎
  where open EqR (HomS {_} {_})

-- this is what we need to show to finally have the complete iso proof.
pp : ∀ n → pNorm n ~~ ⟦ p~ {n} ⟧'
pp zero = refl~~
pp (suc n) = begin
  < vars (sucs (sucs (idFins n))) , q [ p ] >  ≈⟨ cong-<,> refl~ (sym~~ (var-lemma (sucs (idFins n)))) ⟩
  < vars (sucs (idFins n)) ∘ p , q [ p ] >     ≈⟨ cong-<,> refl~ (cong-∘ (pp n) refl~~) ⟩
  < ⟦ vrs (pRen n) ⟧' ∘ p , q [ p ] >          ≈⟨ cong-<,> refl~ (lemmaFins n) ⟩
  < ⟦ vrs (sucRen (pRen n)) ⟧' , q [ p ] >     ∎
  where open EqR (HomS {_} {_})

--  goal: < vars (sucs (sucs (idFins n))) , q [ p ] > ~~
--        < ⟦ vrs (sucRen (sucRen (idRen n))) ⟧' , q [ p ] >


-- to simplify the goal even further: Cu-Cu-Cc-C,
lemm-p : ∀ {n} → pNorm n ~~ ⟦ p~ {n} ⟧'
lemm-p {zero} = refl~~
lemm-p {suc n} = {!!}
