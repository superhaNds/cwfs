module Nary where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Unit

_^_ : ∀ (A : Set) (n : ℕ) → Set
_ ^ zero  = ⊤
A ^ suc n = (A ^ n) × A

proj : ∀ {A : Set} (n : ℕ) (i : Fin n) (S : A ^ n) → A
proj zero () _
proj (suc _) zero    as = proj₂ as
proj (suc n) (suc i) as = proj n i (proj₁ as)

map^ : {A B : Set} (f : A → B) (n : ℕ) (as : A ^ n) → B ^ n
map^ f zero    _  = tt
map^ f (suc n) as = (map^ f n (proj₁ as)) , f (proj₂ as)

id : (n : ℕ) → (Fin n ^ n)
id zero    = tt
id (suc n) = map^ suc n (id n) , zero
