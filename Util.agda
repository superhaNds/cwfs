module Util where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; cong ; sym)
open import Data.Unit using (tt)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec using (Vec ; _∷_ ; [] ; lookup ; map)
open import Function using (_∘_ ; id)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)

-- snoc
_s∷_ : ∀  {n} {A : Set} → Vec A n → A → Vec A (1 + n)
[]       s∷ y = y ∷ []
(x ∷ xs) s∷ y = x ∷ (xs s∷ y)

lookupMap : ∀ {A B : Set} {f : A → B} (n : Nat) (i : Fin n) (xs : Vec A n)
               → f (lookup i xs) ≡ lookup i (map f xs)
lookupMap zero    ()       _
lookupMap (suc n) zero    (x ∷ xs) = refl
lookupMap (suc n) (suc i) (x ∷ xs) = lookupMap n i xs
