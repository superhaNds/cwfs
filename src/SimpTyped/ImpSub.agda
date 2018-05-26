module SimpTyped.ImpSub where

open import Data.Unit using (⊤ ; tt)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import SimpTyped.Context
open import SimpTyped.Type

wk : ∀ {Γ Δ : Ctx} {α} → Γ ⊆ Δ → α ∈ Γ → α ∈ Δ
wk φ v = sub-in φ v

Sub : Ctx → Ctx → Set
Sub Δ ε       = ⊤
Sub Δ (Γ ∙ α) = Sub Δ Γ × α ∈ Δ

weaken : ∀ {Γ : Ctx} {α} → α ∈ Γ → α ∈ (Γ ∙ α)
weaken v = wk ⊆-∙ v

get : ∀ {Γ Δ α} → α ∈ Γ → Sub Δ Γ → α ∈ Δ
get {ε}     ()        γ
get {Γ ∙ x} here      (_ , t) = t
get {Γ ∙ x} (there v) (γ , t) = get v γ

