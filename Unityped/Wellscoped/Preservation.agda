module Unityped.Wellscoped.Preservation where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product
open import Data.Star using (Star; ε; _◅_)
open import Data.Unit
open import Function using (_∘_ ; _$_)
open import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality
open import Unityped.Wellscoped.Syntax
open ≡-Reasoning

------------------------------------------------------
-- Type system

infixr 8 _⇒_

data Ty : Set where
  ♭   : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Nat → Set
Ctx = Vec.Vec Ty

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctx n) : Term n → Ty → Set where

  var : ∀ {i} → Γ ⊢ var i ∈ Vec.lookup i Γ
  
  ƛ   : ∀ {t σ τ} →
  
          σ Vec.∷ Γ ⊢ t ∈ τ →
          ----------------------
              Γ ⊢ ƛ t ∈ σ ⇒ τ
              
  _·_ : ∀ {t₁ t₂ σ τ} →
  
          Γ ⊢ t₁ ∈ σ ⇒ τ → Γ ⊢ t₂ ∈ σ →
          ------------------------------
                Γ ⊢ t₁ · t₂ ∈ τ

module TermApp {T} (l : Lift T Term) where
  open Lift l hiding (var)

  infix 8 _/_

  _/_ : ∀ {m n} → Term m → Sub T m n → Term n
  var i  / ρ = lift (lookup i ρ)
  ƛ t    / ρ = ƛ (t / ρ ↑)
  t · u  / ρ = (t / ρ) · (u / ρ)

  open Application (record { _/_ = _/_ }) using (_/✶_ ; _⊙_)

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

data _▹_⊢_ {n : Nat} : ∀ {m} → Ctx m → Ctx n → Sub Term m n → Set where

  []  : ∀ {Δ} → [] ▹ Δ ⊢ []
  
  _∷_ : ∀ {m} {Γ : Ctx m} {Δ σ t ρ} →
  
          Δ ⊢ t ∈ σ → Γ ▹ Δ ⊢ ρ →
          -----------------------
             σ ∷ Γ ▹ Δ ⊢ t ∷ ρ

module Var where

  map-suc-preserv :
    ∀ {m n Γ Δ σ} (ρ : Sub Fin m n) →
    Γ ▹ Δ ⊢ Vec.map var ρ → Γ ▹ σ ∷ Δ ⊢ Vec.map var (Vec.map suc ρ)
  map-suc-preserv []      []         = []
  map-suc-preserv (x ∷ ρ) (var ∷ ⊢ρ) = var ∷ map-suc-preserv ρ ⊢ρ

  ↑-preserv : ∀ {m n Γ Δ σ} {ρ : Sub Fin m n} →
                    Γ ▹ Δ ⊢ Vec.map var ρ →
                    σ ∷ Γ ▹ σ ∷ Δ ⊢ Vec.map var (VarSubst._↑ ρ)
  ↑-preserv ⊢ρ = var ∷ map-suc-preserv _ ⊢ρ

  id-preserv : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ Vec.map var VarSubst.id
  id-preserv {Γ = []}    = []
  id-preserv {Γ = _ ∷ _} = ↑-preserv id-preserv

  wk-preserv : ∀ {n} {Γ : Ctx n} {σ} →
                 Γ ▹ σ ∷ Γ ⊢ Vec.map var VarSubst.wk
  wk-preserv = map-suc-preserv VarSubst.id id-preserv

  lookup-preserv :
    ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} x ρ →
    Γ ▹ Δ ⊢ Vec.map var ρ → Δ ⊢ var (lookup x ρ) ∈ lookup x Γ
  lookup-preserv zero    (y ∷ ρ) (var ∷ ⊢ρ) = var
  lookup-preserv (suc x) (y ∷ ρ) (var ∷ ⊢ρ) = lookup-preserv x ρ ⊢ρ

  []-preserv : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ t ρ} →
                Γ ⊢ t ∈ σ → Γ ▹ Δ ⊢ Vec.map var ρ → Δ ⊢ t /Var ρ ∈ σ
  []-preserv (var {i}) ⊢ρ = lookup-preserv i _ ⊢ρ
  []-preserv (ƛ t∈)        ⊢ρ = ƛ ([]-preserv t∈ (↑-preserv ⊢ρ))
  []-preserv (t₁∈ · t₂∈)   ⊢ρ = []-preserv t₁∈ ⊢ρ · []-preserv t₂∈ ⊢ρ

weaken-preserv : ∀ {n Γ σ τ} {t : Term n} → Γ ⊢ t ∈ τ → σ ∷ Γ ⊢ weaken t ∈ τ
weaken-preserv t∈ = Var.[]-preserv t∈ Var.wk-preserv

map-weaken-preserv : ∀ {m n Γ Δ σ} {ρ : Sub Term m n} →
                       Γ ▹ Δ ⊢ ρ → Γ ▹ σ ∷ Δ ⊢ Vec.map weaken ρ
map-weaken-preserv []        = []
map-weaken-preserv (t∈ ∷ ⊢ρ) =
  weaken-preserv t∈ ∷ map-weaken-preserv ⊢ρ

↑-preserv : ∀ {m n Γ Δ σ} {ρ : Sub Term m n} →
              Γ ▹ Δ ⊢ ρ → σ ∷ Γ ▹ σ ∷ Δ ⊢ ρ ↑
↑-preserv ⊢ρ = var ∷ map-weaken-preserv ⊢ρ

id-preserv : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ id
id-preserv {Γ = []}    = []
id-preserv {Γ = _ ∷ _} = ↑-preserv id-preserv

p-preserv : ∀ {n σ} {Γ : Ctx n} → Γ ▹ σ ∷ Γ ⊢ Vec.map weaken id
p-preserv {Γ = []}    = []
p-preserv {Γ = x ∷ Γ} = map-weaken-preserv $ ↑-preserv id-preserv

lookup-preserv : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} x {ρ} →
                   Γ ▹ Δ ⊢ ρ → Δ ⊢ lookup x ρ ∈ lookup x Γ
lookup-preserv zero    (t∈ ∷ ⊢ρ) = t∈
lookup-preserv (suc x) (t∈ ∷ ⊢ρ) = lookup-preserv x ⊢ρ

[]-preserv : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ t ρ} →
               Γ ⊢ t ∈ σ → Γ ▹ Δ ⊢ ρ → Δ ⊢ t / ρ ∈ σ
[]-preserv (var {i}) ⊢ρ = lookup-preserv i ⊢ρ
[]-preserv (ƛ t∈)    ⊢ρ = ƛ ([]-preserv t∈ (↑-preserv ⊢ρ))
[]-preserv (t∈ · u∈) ⊢ρ = []-preserv t∈ ⊢ρ · []-preserv u∈ ⊢ρ

cons-preserv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
               {t : Term n} {ρ : Sub Term m n} {σ} →
               Γ ⊢ t ∈ σ → Δ ▹ Γ ⊢ ρ → (σ ∷ Δ) ▹ Γ ⊢ t ∷ ρ
cons-preserv t∈ []       = t∈ ∷ []
cons-preserv t∈ (x ∷ ⊢ρ) = t∈ ∷ cons-preserv x ⊢ρ               

comp-preserv : ∀ {m n k} {Γ : Ctx m} {Δ : Ctx n} {E : Ctx k}
               {ρ : Sub Term m n} {ρ' : Sub Term n k} →
               Γ ▹ Δ ⊢ ρ → Δ ▹ E ⊢ ρ' → Γ ▹ E ⊢ ρ ⊙ ρ'             
comp-preserv [] ⊢ρ' = []
comp-preserv (x ∷ ⊢ρ) ⊢ρ' =
  cons-preserv ([]-preserv x ⊢ρ')
               (comp-preserv ⊢ρ ⊢ρ')

open TermLemmas tmLemmas public hiding (var)
