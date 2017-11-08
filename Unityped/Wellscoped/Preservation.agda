module Unityped.Wellscoped.Preservation where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat
open import Data.Product
open import Data.Star using (Star; ε; _◅_)
open import Data.Unit
open import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality
open import Unityped.Wellscoped.Syntax
open ≡-Reasoning

module TermApp {T} (l : Lift T Term) where
  open Lift l hiding (var)

  infix 8 _/_

  _/_ : ∀ {m n} → Term m → Sub T m n → Term n
  var x   / ρ = lift (lookup x ρ)
  ƛ t     / ρ = ƛ (t / ρ ↑)
  t₁ · t₂ / ρ = (t₁ / ρ) · (t₂ / ρ)

  open Application (record { _/_ = _/_ }) using (_/✶_)

  ƛ-/✶-↑✶ : ∀ k {m n t} (ρs : Subs T m n) →
            ƛ t /✶ ρs ↑✶ k ≡ ƛ (t /✶ ρs ↑✶ suc k)
  ƛ-/✶-↑✶ k ε        = refl
  ƛ-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (ƛ-/✶-↑✶ k ρs) refl

  ·-/✶-↑✶ : ∀ k {m n t₁ t₂} (ρs : Subs T m n) →
            t₁ · t₂ /✶ ρs ↑✶ k ≡ (t₁ /✶ ρs ↑✶ k) · (t₂ /✶ ρs ↑✶ k)
  ·-/✶-↑✶ k ε        = refl
  ·-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (·-/✶-↑✶ k ρs) refl

tmSubst : TermSubst Term
tmSubst = record { var = var; app = TermApp._/_ }

open TermSubst tmSubst hiding (var)

tmLemmas : TermLemmas Term
tmLemmas = record
  { termSubst = tmSubst
  ; app-var   = refl
  ; /✶-↑✶     = Lemma./✶-↑✶
  }
  where
  module Lemma {T₁ T₂} {lift₁ : Lift T₁ Term} {lift₂ : Lift T₂ Term} where

    open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
    open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

    /✶-↑✶ : ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
            (∀ k x → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
             ∀ k t → t     /✶₁ ρs₁ ↑✶₁ k ≡ t     /✶₂ ρs₂ ↑✶₂ k
    /✶-↑✶ ρs₁ ρs₂ hyp k (var x) = hyp k x
    /✶-↑✶ ρs₁ ρs₂ hyp k (ƛ t)   = begin
      ƛ t /✶₁ ρs₁ ↑✶₁ k        ≡⟨ TermApp.ƛ-/✶-↑✶ _ k ρs₁ ⟩
      ƛ (t /✶₁ ρs₁ ↑✶₁ suc k)  ≡⟨ cong ƛ (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) t) ⟩
      ƛ (t /✶₂ ρs₂ ↑✶₂ suc k)  ≡⟨ sym (TermApp.ƛ-/✶-↑✶ _ k ρs₂) ⟩
      ƛ t /✶₂ ρs₂ ↑✶₂ k        ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (t₁ · t₂) = begin
      t₁ · t₂ /✶₁ ρs₁ ↑✶₁ k                    ≡⟨ TermApp.·-/✶-↑✶ _ k ρs₁ ⟩
      (t₁ /✶₁ ρs₁ ↑✶₁ k) · (t₂ /✶₁ ρs₁ ↑✶₁ k)  ≡⟨ cong₂ _·_ (/✶-↑✶ ρs₁ ρs₂ hyp k t₁)
                                                            (/✶-↑✶ ρs₁ ρs₂ hyp k t₂) ⟩
      (t₁ /✶₂ ρs₂ ↑✶₂ k) · (t₂ /✶₂ ρs₂ ↑✶₂ k)  ≡⟨ sym (TermApp.·-/✶-↑✶ _ k ρs₂) ⟩
      t₁ · t₂ /✶₂ ρs₂ ↑✶₂ k                    ∎

infixr 5 _∷_
infix  4 _▹_⊢_

data _▹_⊢_ {n} : ∀ {m} → Ctx m → Ctx n → Sub Term m n → Set where
  []  : ∀ {Δ} → [] ▹ Δ ⊢ []
  _∷_ : ∀ {m} {Γ : Ctx m} {Δ σ t ρ}
        (t∈ : Δ ⊢ t ∈ σ) (⊢ρ : Γ ▹ Δ ⊢ ρ) → σ ∷ Γ ▹ Δ ⊢ t ∷ ρ

module Var where

  map-suc-preserves :
    ∀ {m n Γ Δ σ} (ρ : Sub Fin m n) →
    Γ ▹ Δ ⊢ Vec.map var ρ → Γ ▹ σ ∷ Δ ⊢ Vec.map var (Vec.map suc ρ)
  map-suc-preserves []      []         = []
  map-suc-preserves (x ∷ ρ) (var ∷ ⊢ρ) = var ∷ map-suc-preserves ρ ⊢ρ

  ↑-preserves : ∀ {m n Γ Δ σ} {ρ : Sub Fin m n} →
                    Γ ▹ Δ ⊢ Vec.map var ρ →
                    σ ∷ Γ ▹ σ ∷ Δ ⊢ Vec.map var (VarSubst._↑ ρ)
  ↑-preserves ⊢ρ = var ∷ map-suc-preserves _ ⊢ρ

  id-preserves : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ Vec.map var VarSubst.id
  id-preserves {Γ = []}    = []
  id-preserves {Γ = _ ∷ _} = ↑-preserves id-preserves

  wk-preserves : ∀ {n} {Γ : Ctx n} {σ} →
                 Γ ▹ σ ∷ Γ ⊢ Vec.map var VarSubst.wk
  wk-preserves = map-suc-preserves VarSubst.id id-preserves

  lookup-preserves :
    ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} x ρ →
    Γ ▹ Δ ⊢ Vec.map var ρ → Δ ⊢ var (lookup x ρ) ∈ lookup x Γ
  lookup-preserves zero    (y ∷ ρ) (var ∷ ⊢ρ) = var
  lookup-preserves (suc x) (y ∷ ρ) (var ∷ ⊢ρ) = lookup-preserves x ρ ⊢ρ

  /-preserves : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ t ρ} →
                Γ ⊢ t ∈ σ → Γ ▹ Δ ⊢ Vec.map var ρ → Δ ⊢ t /Var ρ ∈ σ
  /-preserves (var {i}) ⊢ρ = lookup-preserves i _ ⊢ρ
  /-preserves (ƛ t∈)        ⊢ρ = ƛ (/-preserves t∈ (↑-preserves ⊢ρ))
  /-preserves (t₁∈ · t₂∈)   ⊢ρ = /-preserves t₁∈ ⊢ρ · /-preserves t₂∈ ⊢ρ

weaken-preserves : ∀ {n Γ σ τ} {t : Term n} → Γ ⊢ t ∈ τ → σ ∷ Γ ⊢ weaken t ∈ τ
weaken-preserves t∈ = Var./-preserves t∈ Var.wk-preserves

map-weaken-preserves :
  ∀ {m n Γ Δ σ} {ρ : Sub Term m n} →
  Γ ▹ Δ ⊢ ρ → Γ ▹ σ ∷ Δ ⊢ Vec.map weaken ρ
map-weaken-preserves []        = []
map-weaken-preserves (t∈ ∷ ⊢ρ) =
  weaken-preserves t∈ ∷ map-weaken-preserves ⊢ρ

↑-preserves : ∀ {m n Γ Δ σ} {ρ : Sub Term m n} →
              Γ ▹ Δ ⊢ ρ → σ ∷ Γ ▹ σ ∷ Δ ⊢ ρ ↑
↑-preserves ⊢ρ = var ∷ map-weaken-preserves ⊢ρ

id-preserves : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ id
id-preserves {Γ = []}    = []
id-preserves {Γ = _ ∷ _} = ↑-preserves id-preserves

sub-preserves : ∀ {n} {Γ : Ctx n} {σ t} → Γ ⊢ t ∈ σ → σ ∷ Γ ▹ Γ ⊢ sub t
sub-preserves t∈ = t∈ ∷ id-preserves

lookup-preserves :
  ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} x {ρ} →
  Γ ▹ Δ ⊢ ρ → Δ ⊢ lookup x ρ ∈ lookup x Γ
lookup-preserves zero    (t∈ ∷ ⊢ρ) = t∈
lookup-preserves (suc x) (t∈ ∷ ⊢ρ) = lookup-preserves x ⊢ρ

/-preserves : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ t ρ} →
              Γ ⊢ t ∈ σ → Γ ▹ Δ ⊢ ρ → Δ ⊢ t / ρ ∈ σ
/-preserves (var {i}) ⊢ρ = lookup-preserves i ⊢ρ
/-preserves (ƛ t∈)        ⊢ρ = ƛ (/-preserves t∈ (↑-preserves ⊢ρ))
/-preserves (t₁∈ · t₂∈)   ⊢ρ = /-preserves t₁∈ ⊢ρ · /-preserves t₂∈ ⊢ρ

open TermLemmas tmLemmas public hiding (var)
