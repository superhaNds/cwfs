-----------------------------------------------------------------------
-- The raw grammar and substitutions using the standard library modules
-- for substitutions
-----------------------------------------------------------------------
module Ext-Typed.DTyped.LambdaSLIB where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Product
open import Data.Star using (Star; ε; _◅_)
open import Data.Unit
open import Data.Vec as Vec hiding ([_])
open import Relation.Binary.PropositionalEquality as PropEq 
  using (_≡_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning

infix 10 _·_

data Tm (n : Nat) : Set where
  var : (i : Fin n) → Tm n
  ƛ   : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n
  Π   : Tm n → Tm (suc n) → Tm n
  U   : Tm n

module TmApp {T} (l : Lift T Tm) where
  open Lift l hiding (var)

  infix 8 _[_]
  
  _[_] : ∀ {m n} → Tm m → Sub T m n → Tm n
  var i   [ ρ ] = lift (lookup i ρ)
  ƛ t     [ ρ ] = ƛ (t [ ρ ↑ ])
  (t · u) [ ρ ] = (t [ ρ ]) · (u [ ρ ])
  Π A B   [ ρ ] = Π (A [ ρ ]) (B [ ρ ↑ ])
  U       [ _ ] = U

  open Application (record { _/_ = _[_] }) using (_/✶_)

  ƛ-/✶-↑✶ : ∀ k {m n t} (ρs : Subs T m n) →
            ƛ t /✶ ρs ↑✶ k ≡ ƛ (t /✶ ρs ↑✶ suc k)
  ƛ-/✶-↑✶ k ε        = refl
  ƛ-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _[_] (ƛ-/✶-↑✶ k ρs) refl

  ·-/✶-↑✶ : ∀ k {m n t₁ t₂} (ρs : Subs T m n) →
            t₁ · t₂ /✶ ρs ↑✶ k ≡ (t₁ /✶ ρs ↑✶ k) · (t₂ /✶ ρs ↑✶ k)
  ·-/✶-↑✶ k ε        = refl
  ·-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _[_] (·-/✶-↑✶ k ρs) refl

  Π-/✶-↑✶ : ∀ k {m n A B} (ρs : Subs T m n) →
            Π A B /✶ ρs ↑✶ k ≡ Π (A /✶ ρs ↑✶ k) (B /✶ ρs ↑✶ suc k)
  Π-/✶-↑✶ k ε = refl
  Π-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _[_] (Π-/✶-↑✶ k ρs) refl          

  U-/✶-↑✶ : ∀ k {m n} (ρs : Subs T m n) →
            U /✶ ρs ↑✶ k ≡ U
  U-/✶-↑✶ k ε = refl
  U-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _[_] (U-/✶-↑✶ k ρs) refl            

tmSubst : TermSubst Tm
tmSubst = record { var = var; app = TmApp._[_] }

open TermSubst tmSubst hiding (var)

tmLemmas : TermLemmas Tm
tmLemmas = record
  { termSubst = tmSubst
  ; app-var   = refl
  ; /✶-↑✶     = Lemma./✶-↑✶
  }
  where
  module Lemma {T₁ T₂} {lift₁ : Lift T₁ Tm} {lift₂ : Lift T₂ Tm} where

    open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
    open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

    /✶-↑✶ : ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
            (∀ k x → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
             ∀ k t → t     /✶₁ ρs₁ ↑✶₁ k ≡ t     /✶₂ ρs₂ ↑✶₂ k
    /✶-↑✶ ρs₁ ρs₂ hyp k (var i) = hyp k i
    /✶-↑✶ ρs₁ ρs₂ hyp k (ƛ t) = begin
      ƛ t /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ TmApp.ƛ-/✶-↑✶ _ k ρs₁ ⟩
      ƛ (t /✶₁ ρs₁ ↑✶₁ suc k)
        ≡⟨ cong ƛ (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) t) ⟩
      ƛ (t /✶₂ ρs₂ ↑✶₂ suc k)
        ≡⟨ sym (TmApp.ƛ-/✶-↑✶ _ k ρs₂) ⟩
      ƛ t /✶₂ ρs₂ ↑✶₂ k
        ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (t₁ · t₂) = begin
      t₁ · t₂ /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ TmApp.·-/✶-↑✶ _ k ρs₁ ⟩
      (t₁ /✶₁ ρs₁ ↑✶₁ k) · (t₂ /✶₁ ρs₁ ↑✶₁ k)
        ≡⟨ cong₂ _·_ (/✶-↑✶ ρs₁ ρs₂ hyp k t₁) (/✶-↑✶ ρs₁ ρs₂ hyp k t₂) ⟩
      (t₁ /✶₂ ρs₂ ↑✶₂ k) · (t₂ /✶₂ ρs₂ ↑✶₂ k)
        ≡⟨ sym (TmApp.·-/✶-↑✶ _ k ρs₂) ⟩
      t₁ · t₂ /✶₂ ρs₂ ↑✶₂ k
        ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (Π A B) = begin
      Π A B /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ TmApp.Π-/✶-↑✶ _ k ρs₁ ⟩
      Π (A /✶₁ ρs₁ ↑✶₁ k) (B /✶₁ ρs₁ ↑✶₁ suc k)
        ≡⟨ cong₂ Π (/✶-↑✶ ρs₁ ρs₂ hyp k A) (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) B) ⟩
      Π (A /✶₂ ρs₂ ↑✶₂ k) (B /✶₂ ρs₂ ↑✶₂ suc k)
        ≡⟨ sym (TmApp.Π-/✶-↑✶ _ k ρs₂) ⟩
      Π A B /✶₂ ρs₂ ↑✶₂ k
        ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k U = begin
      U /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ TmApp.U-/✶-↑✶ _ k ρs₁ ⟩
      U
        ≡⟨ sym (TmApp.U-/✶-↑✶ _ k ρs₂) ⟩
      U /✶₂ ρs₂ ↑✶₂ k
        ∎
