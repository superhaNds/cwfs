module ExtDepTyped.Raw.PiUcwf where

open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Unityped.Ucwf

record Π-λβη-ucwf : Set₁ where
  field
    λucwf : λβη-ucwf
  open λβη-ucwf λucwf using (ucwf)
  open Ucwf ucwf
  field
    Π : ∀ {n} → Tm n → Tm (suc n) → Tm n
    U : ∀ {n} → Tm n

    subU : ∀ {m n} {σ : Sub m n} → U [ σ ] ~ U
    
    subΠ : ∀ {m n} {σ : Sub m n} {A B} → (Π A B) [ σ ] ~ Π (A [ σ ]) (B [ ⇑ σ ])

    cong-Π : ∀ {n} {A A' : Tm n} {B B'}
             → A ~ A'
             → B ~ B'
             → Π A B ~ Π A' B'
