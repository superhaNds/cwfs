module Proj where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Data.Vec hiding ([_])
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Definitions

-----------------------------------------------------
-- Peter's proof that the 'normalized' version of p is indeed p

-- ≈ = "\eq4"
var-lemma : ∀ {m n} (is : Fins m n) → vars is ∘ p ~~ vars (sucs is)
var-lemma <> = ∘<> p
var-lemma < is , i > = begin
  < vars is , varCwf i > ∘ p
    ≈⟨ maps (varCwf i) (vars is) p ⟩
  < vars is ∘ p , varCwf i [ p ] >
    ≈⟨ cong-<,> refl~ (var-lemma is) ⟩
  < vars (sucs is) , varCwf (suc i) >
    ≈⟨ refl~~ ⟩
  vars (sucs < is , i > )
    ∎
  where open EqR (HomS {_} {_})

help : ∀ {n} → _~~_ {m = n} (vars (mapFins (mapFins (tab (λ z → z)) suc) suc)) (vars (mapFins (tab suc) suc))
help {n} rewrite sym (tabulate-∘ {n} suc (λ x → x)) = refl~~

p~vars : ∀ n → p ~~ pNorm n
p~vars zero = hom-0~<> (p {0})
p~vars (suc n) = begin
  p
    ≈⟨ surj-<,> p ⟩
  < p ∘ p , q [ p ] >
    ≈⟨ cong-<,> refl~ (cong-∘ (p~vars n) (refl~~)) ⟩
  < vars (mapFins (tab (λ z → z)) suc) ∘ p , q [ p ] >
    ≈⟨ cong-<,> refl~ (var-lemma (mapFins (tab (λ z → z)) suc)) ⟩
  < vars (mapFins (mapFins (tab (λ z → z)) suc) suc) , q [ p ] >
    ≈⟨ cong-<,> refl~ help ⟩
  < vars (mapFins (tab suc) suc) , q [ p ] >
    ∎
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

vars-map : ∀ {m n} (is : Fins m n) → vars is ~~ mapT varCwf is
vars-map <>         = refl~~
vars-map < is , x > = cong-<,> refl~ (vars-map is)

map-map : ∀ {m n} (is : Fins m n)
          → ⟦ mapTT var is ⟧' ~~ mapT varCwf is
map-map <>         = refl~~
map-map < is , x > = cong-<,> refl~ (map-map is)

lm-p : ∀ n → vars (pFins n) ~~ ⟦ mapTT var (pFins n) ⟧'
lm-p n = trans~~ (vars-map (pFins n)) (sym~~ (map-map (pFins n)))

lookup-fn-map : ∀ {m n} (i : Fin n) (is : Fins m n) (f : Fin m → Tm m) →
                lookup i (mapTT f is) ≡ f (lookup-fn i is)
lookup-fn-map zero < is , x > f = refl
lookup-fn-map (suc i) < is , x > f = lookup-fn-map i is f

lookup-fn-pf : ∀ {n} (i : Fin n) → lookup-fn i (pFins n) ≡ suc i
lookup-fn-pf i = begin
  lookup-fn i (mapFins (tab (λ z → z)) suc) ≡⟨ cong (lookup-fn i) (sym (tabulate-∘ suc (λ z → z))) ⟩
  lookup-fn i (tab (λ x → suc x)) ≡⟨ lookup∘tab suc i ⟩
  suc i ∎
  where open P.≡-Reasoning

final : ∀ {n} (i : Fin n) → lookup i (mapTT var (pFins n)) ≡ var (suc i)
final i = begin
  lookup i (mapTT var (pFins _)) ≡⟨ lookup-fn-map i (pFins _) var ⟩
  var (lookup-fn i (pFins _))    ≡⟨ cong var (lookup-fn-pf i) ⟩
  var (suc i) ∎
  where open P.≡-Reasoning
