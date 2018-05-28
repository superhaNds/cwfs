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

record Π-λβη-ucwf-⇒ (src trg : Π-λβη-ucwf) : Set₁ where
  open Π-λβη-ucwf src renaming (λucwf to λucwf₁ ; Π to Π₁ ; U to U₁)
  open Π-λβη-ucwf trg renaming (λucwf to λucwf₂ ; Π to Π₂ ; U to U₂)
  open λβη-ucwf λucwf₁ renaming (ucwf to ucwf₁)
  open λβη-ucwf λucwf₂ renaming (ucwf to ucwf₂)
  open Ucwf ucwf₁ renaming (Tm to Tm₁ ; _~_ to _~₁_)
  open Ucwf ucwf₂ renaming (Tm to Tm₂ ; _~_ to _~₂_)
  field
    λucwf-⇒ : λβη-ucwf-⇒ λucwf₁ λucwf₂
  open λβη-ucwf-⇒ λucwf-⇒
  open Ucwf-⇒ ucwf-⇒
  field
    U-preserved : ∀ {n} → ⟦ U₁ ⟧ ~₂ U₂ {n}
    Π-preserved : ∀ {n} {A : Tm₁ n} {B} → ⟦ Π₁ A B ⟧ ~₂ Π₂ ⟦ A ⟧ ⟦ B ⟧

record Π-λβη-ucwf-≅ {Πu₁ Πu₂} (Πu₁-⇒ : Π-λβη-ucwf-⇒ Πu₁ Πu₂)
                              (Πu₂-⇒ : Π-λβη-ucwf-⇒ Πu₂ Πu₁) : Set₁ where
  open Π-λβη-ucwf Πu₁ renaming (λucwf to λu₁)
  open Π-λβη-ucwf Πu₂ renaming (λucwf to λu₂)
  open Π-λβη-ucwf-⇒ Πu₁-⇒ renaming (λucwf-⇒ to λu₁-⇒)
  open Π-λβη-ucwf-⇒ Πu₂-⇒ renaming (λucwf-⇒ to λu₂-⇒)
  open λβη-ucwf-⇒ λu₁-⇒ renaming (ucwf-⇒ to u₁-⇒)
  open λβη-ucwf-⇒ λu₂-⇒ renaming (ucwf-⇒ to u₂-⇒)
  open Ucwf-⇒ u₁-⇒ renaming (⟦_⟧ to ⟦_⟧₁ ; ⟦_⟧' to ⟦_⟧'₁)
  open Ucwf-⇒ u₂-⇒ renaming (⟦_⟧ to ⟦_⟧₂ ; ⟦_⟧' to ⟦_⟧'₂)
  open λβη-ucwf λu₁ renaming (ucwf to u₁)
  open λβη-ucwf λu₂ renaming (ucwf to u₂)
  open Ucwf u₁ renaming (Tm to Tm₁ ; Sub to Sub₁ ; _~_ to _~₁_ ; _≈_ to _≈₁_)
  open Ucwf u₂ renaming (Tm to Tm₂ ; Sub to Sub₂ ; _~_ to _~₂_ ; _≈_ to _≈₂_)
  field
    left-inv-tm   : ∀ {n} (t : Tm₁ n) → ⟦ ⟦ t ⟧₁ ⟧₂ ~₁ t
    right-inv-tm  : ∀ {n} (t : Tm₂ n) → ⟦ ⟦ t ⟧₂ ⟧₁ ~₂ t
    
    left-inv-sub  : ∀ {m n} (σ : Sub₁ m n) → ⟦ ⟦ σ ⟧'₁ ⟧'₂ ≈₁ σ
    right-inv-sub : ∀ {m n} (σ : Sub₂ m n) → ⟦ ⟦ σ ⟧'₂ ⟧'₁ ≈₂ σ

