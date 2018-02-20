-------------------------------------------------------------------
-- Proofs for the projection inverse
-------------------------------------------------------------------
module Unityped.Projection where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin
open import Function as F using (_$_ ; id)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P

-------------------------------------------------------------------
-- snoc sequences of fins

module Fins where

  data Fins : Nat → Nat → Set where
    <>    : ∀ {m} → Fins m 0
    <_,_> : ∀ {m n} → Fins m n → Fin m → Fins m (suc n)
  
  mapFins : ∀ {n m k} (is : Fins m n) (f : Fin m → Fin k) → Fins k n
  mapFins <>         f = <>
  mapFins < is , x > f = < mapFins is f , f x >
  
  tab : ∀ {n m} → (Fin n → Fin m) → Fins m n
  tab {zero}  f = <>
  tab {suc n} f = < (tab (f F.∘ suc)) , (f zero) >

  sucs : ∀ {m n} → Fins m n → Fins (suc m) n
  sucs is = mapFins is suc

  idFins : ∀ n → Fins n n
  idFins n = tab id

  pFins : ∀ n → Fins (suc n) n
  pFins n = sucs (idFins n)

  lookup-fn : ∀ {m n} → Fin n → Fins m n → Fin m
  lookup-fn zero    < is , x > = x
  lookup-fn (suc i) < is , x > = lookup-fn i is

  idFins' : ∀ {n} → Fins n n
  idFins' = tab id

  lookup∘tab : ∀ {m n} (f : Fin n → Fin m) (i : Fin n) →
               lookup-fn i (tab f) P.≡ f i
  lookup∘tab f zero = P.refl
  lookup∘tab f (suc i) = lookup∘tab (λ z → f (suc z)) i

  tabulate-∘ : ∀ {n m k}
               (f : Fin m → Fin k) (g : Fin n → Fin m) →
               tab (λ x → f (g x)) P.≡ mapFins (tab g) f
  tabulate-∘ {zero} f g = P.refl
  tabulate-∘ {suc n} f g = P.cong (<_, f (g zero) >) (tabulate-∘ f (λ z → g (suc z)))

open Fins

-------------------------------------------------------------------
-- Proof that p is convertible to its normal form

module PProof where

  open import Unityped.UcwfComb renaming (Tm to Tm-cwf)

  varCwf : ∀ {n} (i : Fin n) → Tm-cwf n
  varCwf zero    = q
  varCwf (suc i) = varCwf i [ p ]

  vars : ∀ {n m} (is : Fins m n) → Sub m n
  vars <>         = <>
  vars < is , i > = < vars is , varCwf i >

  pNorm : ∀ n → Sub (suc n) n
  pNorm n = vars (pFins n)

  mapT : ∀ {n m} (f : Fin m → Tm-cwf m) (is : Fins m n) → Sub m n
  mapT f <>         = <>
  mapT f < is , x > = < mapT f is , f x >
  
  vars-map : ∀ {m n} (is : Fins m n) → vars is ≋ mapT varCwf is
  vars-map <>         = refl≋
  vars-map < is , x > = cong-<,> refl≈ (vars-map is)

  var-lemma : ∀ {m n} (is : Fins m n) → vars is ∘ p ≋ vars (sucs is)
  var-lemma <>         = <>Lzero p
  var-lemma < is , i > = begin
    < vars is , varCwf i > ∘ p
      ≈⟨ compExt (vars is) p (varCwf i) ⟩
    < vars is ∘ p , varCwf i [ p ] >
      ≈⟨ cong-<,> refl≈ (var-lemma is) ⟩
    < vars (sucs is) , varCwf (suc i) >
      ≈⟨ refl≋ ⟩
    vars (sucs < is , i > )
      ∎
    where open EqR (SubSetoid {_} {_})

  help : ∀ {n} → _≋_ {m = n} (vars (mapFins (mapFins (tab F.id) suc) suc))
                             (vars (mapFins (tab suc) suc))
  help {n} rewrite P.sym (tabulate-∘ {n} suc F.id) = refl≋

  p~vars : ∀ n → p ≋ pNorm n
  p~vars zero    = ter-arrow (p {0})
  p~vars (suc n) = begin
    p
      ≈⟨ surj-<,> p ⟩
    < p ∘ p , q [ p ] >
      ≈⟨ cong-<,> refl≈ (cong-∘ (p~vars n) (refl≋)) ⟩
    < vars (mapFins (tab F.id) suc) ∘ p , q [ p ] >
      ≈⟨ cong-<,> refl≈ (var-lemma (mapFins (tab F.id) suc)) ⟩
    < vars (mapFins (mapFins (tab F.id) suc) suc) , q [ p ] >
      ≈⟨ cong-<,> refl≈ help ⟩
    < vars (mapFins (tab suc) suc) , q [ p ] >
      ∎
    where open EqR (SubSetoid {_} {_})
    
