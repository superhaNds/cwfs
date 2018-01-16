-------------------------------------------------------------------------
-- Raw terms indexed by the maximum number of free variables they may
-- contain. Provides a basis for the "extrinsic" approach of implementing
-- simply typed and dependently typed calculi and the corresponding cwf
-------------------------------------------------------------------------
module Ext-Typed.Raw where

open import Data.Nat
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Star using (Star; ε; _◅_)
open import Data.Vec as Vec hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Ext-Typed.Syntax
open ≡-Reasoning

-------------------------------------------------------------------------
-- Using the standard library of Substitution: operations and lemmas

module TermApp {T} (l : Lift T Term) where
  open Lift l hiding (var)

  infix 8 _[_]

  _[_] : ∀ {m n} → Term m → Sub T m n → Term n
  var i  [ ρ ] = lift (lookup i ρ)
  ƛ t    [ ρ ] = ƛ (t [ ρ ↑ ])
  t · u  [ ρ ] = (t [ ρ ]) · (u [ ρ ])

  open Application (record { _/_ = _[_] }) using (_/✶_ ; _⊙_)

  ƛ-/✶-↑✶ : ∀ k {m n t} (ρs : Subs T m n) →
            ƛ t /✶ ρs ↑✶ k ≡ ƛ (t /✶ ρs ↑✶ suc k)
  ƛ-/✶-↑✶ k ε        = refl
  ƛ-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _[_] (ƛ-/✶-↑✶ k ρs) refl

  ·-/✶-↑✶ : ∀ k {m n t₁ t₂} (ρs : Subs T m n) →
            t₁ · t₂ /✶ ρs ↑✶ k ≡ (t₁ /✶ ρs ↑✶ k) · (t₂ /✶ ρs ↑✶ k)
  ·-/✶-↑✶ k ε        = refl
  ·-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _[_] (·-/✶-↑✶ k ρs) refl

tmSubst : TermSubst Term
tmSubst = record { var = var; app = TermApp._[_] }

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
      ƛ t /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ TermApp.ƛ-/✶-↑✶ _ k ρs₁ ⟩
      ƛ (t /✶₁ ρs₁ ↑✶₁ suc k)
        ≡⟨ cong ƛ (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) t) ⟩
      ƛ (t /✶₂ ρs₂ ↑✶₂ suc k)
        ≡⟨ sym (TermApp.ƛ-/✶-↑✶ _ k ρs₂) ⟩
      ƛ t /✶₂ ρs₂ ↑✶₂ k
        ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (t₁ · t₂) = begin
      t₁ · t₂ /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ TermApp.·-/✶-↑✶ _ k ρs₁ ⟩
      (t₁ /✶₁ ρs₁ ↑✶₁ k) · (t₂ /✶₁ ρs₁ ↑✶₁ k)
        ≡⟨ cong₂ _·_ (/✶-↑✶ ρs₁ ρs₂ hyp k t₁) (/✶-↑✶ ρs₁ ρs₂ hyp k t₂) ⟩
      (t₁ /✶₂ ρs₂ ↑✶₂ k) · (t₂ /✶₂ ρs₂ ↑✶₂ k)
        ≡⟨ sym (TermApp.·-/✶-↑✶ _ k ρs₂) ⟩
      t₁ · t₂ /✶₂ ρs₂ ↑✶₂ k
        ∎
