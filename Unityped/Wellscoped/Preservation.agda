module Unityped.Wellscoped.Preservation where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product hiding (_,_)
open import Data.Star using (Star; ε; _◅_)
open import Data.Unit
open import Function using (_∘_ ; _$_)
open import Data.Vec as Vec hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
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

_,_ : ∀ {n} (Γ : Ctx n) (α : Ty) → Ctx (suc n)
Γ , α = α Vec.∷ Γ

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctx n) : Term n → Ty → Set where

  var : ∀ {i} → Γ ⊢ var i ∈ Vec.lookup i Γ
  
  ƛ   : ∀ {t α β} →
  
          Γ , α ⊢ t ∈ β →
          ----------------------
              Γ ⊢ ƛ t ∈ α ⇒ β
              
  _·_ : ∀ {t u σ τ} →
  
          Γ ⊢ t ∈ σ ⇒ τ → Γ ⊢ u ∈ σ →
          ------------------------------
                Γ ⊢ t · u ∈ τ

⊢vr0 : ∀ {n α} {Γ : Ctx n} → Γ , α ⊢ q ∈ α
⊢vr0 = var

⊢vrn : ∀ {n α β} {i : Fin n} {Γ : Ctx n} → Γ ⊢ var i ∈ β →
       Γ , α ⊢ var (suc i) ∈ β
⊢vrn var = var

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

infix  4 _▹_⊢_

data _▹_⊢_ {n} : ∀ {m} → Ctx m → Ctx n → Sub Term m n → Set where

  []  : ∀ {Δ} → [] ▹ Δ ⊢ []
  
  ext : ∀ {m} {Γ : Ctx m} {Δ σ t ρ} →
  
          Δ ⊢ t ∈ σ → Γ ▹ Δ ⊢ ρ →
          -----------------------
             Γ , σ ▹ Δ ⊢ t ∷ ρ

_[_] : {m n : Nat} → Term m → Sub Term m n → Term n
_[_] = _/_

module Var where

  map-suc-preserv : ∀ {m n Γ Δ α} (ρ : Sub Fin m n) →
                    Γ ▹ Δ ⊢ Vec.map var ρ →
                    Γ ▹ α ∷ Δ ⊢ Vec.map var (Vec.map suc ρ)
  map-suc-preserv []      []           = []
  map-suc-preserv (x ∷ ρ) (ext var ⊢ρ) = ext var (map-suc-preserv ρ ⊢ρ)

  ↑-preserv : ∀ {m n Γ Δ α} {ρ : Sub Fin m n} →
              Γ ▹ Δ ⊢ Vec.map var ρ →
              Γ , α ▹ Δ , α ⊢ Vec.map var (VarSubst._↑ ρ)
  ↑-preserv ⊢ρ = ext var (map-suc-preserv _ ⊢ρ)

  id-preserv : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ Vec.map var VarSubst.id
  id-preserv {Γ = []}    = []
  id-preserv {Γ = _ ∷ _} = ↑-preserv id-preserv

  wk-preserv : ∀ {n} {Γ : Ctx n} {α} →
               Γ ▹ Γ , α ⊢ Vec.map var VarSubst.wk
  wk-preserv = map-suc-preserv VarSubst.id id-preserv

  lookup-preserv : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} x ρ →
                   Γ ▹ Δ ⊢ Vec.map var ρ → Δ ⊢ var (lookup x ρ) ∈ lookup x Γ
  lookup-preserv zero    (_ ∷ _) (ext var _) = var
  lookup-preserv (suc x) (_ ∷ ρ) (ext var ⊢ρ) = lookup-preserv x ρ ⊢ρ

  []-preserv : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {α t ρ} →
               Γ ⊢ t ∈ α → Γ ▹ Δ ⊢ Vec.map var ρ → Δ ⊢ t /Var ρ ∈ α
  []-preserv (var {i}) ⊢ρ = lookup-preserv i _ ⊢ρ
  []-preserv (ƛ t)     ⊢ρ = ƛ ([]-preserv t (↑-preserv ⊢ρ))
  []-preserv (t · u)   ⊢ρ = []-preserv t ⊢ρ · []-preserv u ⊢ρ

weaken-preserv : ∀ {n Γ α β} {t : Term n} →
                 Γ ⊢ t ∈ β → Γ , α ⊢ weaken t ∈ β
weaken-preserv t = Var.[]-preserv t Var.wk-preserv

map-weaken-preserv : ∀ {m n Γ Δ α} {ρ : Sub Term m n} →
                     Γ ▹ Δ ⊢ ρ → Γ ▹ Δ , α ⊢ Vec.map weaken ρ
map-weaken-preserv []         = []
map-weaken-preserv (ext t ⊢ρ) =
  ext (weaken-preserv t) (map-weaken-preserv ⊢ρ)

↑-preserv : ∀ {m n Γ Δ α} {ρ : Sub Term m n} →
            Γ ▹ Δ ⊢ ρ → Γ , α ▹ Δ , α ⊢ ρ ↑
↑-preserv ⊢ρ = ext var (map-weaken-preserv ⊢ρ)

id-preserv : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ id
id-preserv {Γ = []}    = []
id-preserv {Γ = _ ∷ _} = ↑-preserv id-preserv

p-preserv : ∀ {n α} {Γ : Ctx n} → Γ ▹ Γ , α ⊢ Vec.map weaken id
p-preserv {Γ = []}    = []
p-preserv {Γ = x ∷ Γ} = map-weaken-preserv $ ↑-preserv id-preserv

lookup-preserv : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} i {ρ} →
                 Γ ▹ Δ ⊢ ρ → Δ ⊢ lookup i ρ ∈ lookup i Γ
lookup-preserv zero    (ext t ⊢ρ) = t
lookup-preserv (suc x) (ext t ⊢ρ) = lookup-preserv x ⊢ρ

subst-lemma : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {α t ρ} →
              Γ ⊢ t ∈ α → Γ ▹ Δ ⊢ ρ → Δ ⊢ t [ ρ ] ∈ α
subst-lemma (var {i}) ⊢ρ = lookup-preserv i ⊢ρ
subst-lemma (ƛ t)     ⊢ρ = ƛ (subst-lemma t (↑-preserv ⊢ρ))
subst-lemma (t · u)   ⊢ρ = subst-lemma t ⊢ρ · subst-lemma u ⊢ρ

∙-preserv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
            {t : Term n} {ρ : Sub Term m n} {α} →
            Γ ⊢ t ∈ α → Δ ▹ Γ ⊢ ρ → Δ , α ▹ Γ ⊢ t ∷ ρ
∙-preserv t []         = ext t []
∙-preserv t (ext x ⊢ρ) = ext t (∙-preserv x ⊢ρ)

⋆-preserv : ∀ {m n k} {Γ : Ctx m} {Δ : Ctx n} {E : Ctx k}
            {ρ : Sub Term m n} {ρ' : Sub Term n k} →
            Γ ▹ Δ ⊢ ρ → Δ ▹ E ⊢ ρ' → Γ ▹ E ⊢ ρ ⊙ ρ'             
⋆-preserv []         _   = []
⋆-preserv (ext x ⊢ρ) ⊢ρ' =
  ∙-preserv (subst-lemma x ⊢ρ')
            (⋆-preserv ⊢ρ ⊢ρ')

open TermLemmas tmLemmas public hiding (var)
