module Util where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong)
open import Data.Unit
open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec
open import Function using (_∘_ ; id)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Nary using (_^_)

record _≅_ (A B : Set) : Set₁ where
  field
    to    : A → B
    from  : B → A
    inv₁  : ∀ (a : A) → a ≡ from (to a)
    inv₂  : ∀ (b : B) → b ≡ to (from b)

ref≅ : ∀ {A} → A ≅ A
ref≅ = record { to   = id
              ; from = id
              ; inv₁ = λ _ → refl
              ; inv₂ = λ _ → refl }

sym≅ : ∀ {A B} → A ≅ B → B ≅ A
sym≅ record { to = f ; from = g ; inv₁ = φ; inv₂ = ψ }
  = record { to   = g
           ; from = f
           ; inv₁ = ψ
           ; inv₂ = φ }

trans≅ : ∀ {A B C} → A ≅ B → B ≅ C → A ≅ C
trans≅ record { to = f₁ ; from = g₁ ; inv₁ = φ₁ ; inv₂ = ψ₁ }
       record { to = f₂ ; from = g₂ ; inv₁ = φ₂ ; inv₂ = ψ₂ }
  = record { to   = f₂ ∘ f₁
           ; from = g₁ ∘ g₂
           ; inv₁ = λ a → trans (φ₁ a) (cong g₁ (φ₂ (f₁ a)))
           ; inv₂ = λ c → trans (ψ₂ c) (cong f₂ (ψ₁ (g₂ c))) }

-----------------------------------------------------------------------

^2Vec : {A : Set} (n : Nat) → A ^ n → Vec A n
^2Vec zero    as = []
^2Vec (suc n) as = proj₂ as ∷ ^2Vec n (proj₁ as)

vec2^ : {A : Set} (n : Nat) → Vec A n → A ^ n
vec2^ _ []       = tt
vec2^ _ (a ∷ as) = vec2^ _ as , a

vec≅^ : ∀ {A n} → (Vec A n) ≅ (A ^ n)
vec≅^ {A} {n} = record { to = vec2^ n ; from = ^2Vec n ; inv₁ = inv1 ; inv₂ = inv2 }
  where inv1 : ∀ {A} {n} (v : Vec A n) → v ≡ ^2Vec n (vec2^ n v)
        inv1 {_} {_} []      = refl
        inv1 {_} {_} (x ∷ xs) = cong (_∷_ x) (inv1 xs)
        inv2 : ∀ {A} {n} (a : A ^ n) → a ≡ vec2^ n (^2Vec n a)
        inv2 {_} {zero}  tt        = refl
        inv2 {_} {suc n} (a , a^n) = cong (λ x → x , a^n) (inv2 a)

-----------------------------------------------------------------------

-- snoc
_s∷_ : ∀  {n} {A : Set} → Vec A n → A → Vec A (1 + n)
[]       s∷ y = y ∷ []
(x ∷ xs) s∷ y = x ∷ (xs s∷ y)
