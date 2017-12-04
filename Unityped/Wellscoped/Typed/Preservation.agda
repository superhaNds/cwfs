module Unityped.Wellscoped.Typed.Preservation where

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
Γ , α = α ∷ Γ

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctx n) : Term n → Ty → Set where

  var : ∀ {i} → Γ ⊢ var i ∈ lookup i Γ
  
  ƛ   : ∀ {t α β} →
  
             Γ , α ⊢ t ∈ β →
           -------------------
             Γ ⊢ ƛ t ∈ α ⇒ β
              
  _·_ : ∀ {t u σ τ} →
  
           Γ ⊢ t ∈ σ ⇒ τ → Γ ⊢ u ∈ σ →
          -----------------------------
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


SubT : Nat → Nat → Set
SubT m n = Sub Term n m

Ren : Nat → Nat → Set
Ren m n = Sub Fin n m

wk-ren : ∀ {m n} → Ren m n → Ren (suc m) n
wk-ren ρ = Vec.map suc ρ

ren-to-sub : ∀ {m n} → Ren m n → SubT m n
ren-to-sub ρ = Vec.map var ρ

wk-vars : ∀ {m n} → Ren m n → SubT (suc m) n
wk-vars = ren-to-sub ∘ wk-ren

_[_] : {m n : Nat} → Term m → SubT n m → Term n
_[_] = _/_

_∙_ : ∀ {m n} (ρ : SubT m n) (t : Term m) → SubT m (suc n)
ρ ∙ t = t ∷ ρ

_⋆_ : ∀ {m n k} → SubT n k → SubT m n → SubT m k
ρ₁ ⋆ ρ₂ = ρ₁ ⊙ ρ₂

p : ∀ {n} → SubT (suc n) n
p = wk

wkn : ∀ {n} → Term n → Term (suc n)
wkn = weaken

infix  4 _▹_⊢_

data _▹_⊢_ {n} : ∀ {m} → Ctx m → Ctx n → SubT n m → Set where

  []  : ∀ {Δ} → [] ▹ Δ ⊢ []
  
  ext : ∀ {m} {Γ : Ctx m} {Δ σ t ρ} →
  
          Δ ⊢ t ∈ σ → Γ ▹ Δ ⊢ ρ →
          -----------------------
             Γ , σ ▹ Δ ⊢ ρ ∙ t

--------------------------------------------------------------------------------
-- Typing rules for scwf

module Var where

  map-suc-preserv : ∀ {m n Γ Δ α} (ρ : Sub Fin m n) →
                    Γ ▹ Δ ⊢ Vec.map var ρ →
                    Γ ▹ Δ , α ⊢ Vec.map var (Vec.map suc ρ)
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

p-preserv : ∀ {n α} {Γ : Ctx n} → Γ ▹ Γ , α ⊢ p
p-preserv {Γ = []}    = []
p-preserv {Γ = _ ∷ Γ} = map-weaken-preserv $ ↑-preserv id-preserv

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
            Γ ⊢ t ∈ α → Δ ▹ Γ ⊢ ρ → Δ , α ▹ Γ ⊢ ρ ∙ t
∙-preserv t ⊢ρ = ext t ⊢ρ

⋆-preserv : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
              {ρ : SubT n k} {σ : SubT m n} →
            Θ ▹ Γ ⊢ ρ → Γ ▹ Δ ⊢ σ → Θ ▹ Δ ⊢ ρ ⋆ σ
⋆-preserv []         _   = []
⋆-preserv (ext x ⊢ρ) ⊢ρ' =
  ∙-preserv (subst-lemma x ⊢ρ')
            (⋆-preserv ⊢ρ ⊢ρ')

open TermLemmas tmLemmas public hiding (var)

wk-[p] : ∀ {n} (t : Term n) → t [ p ] ≡ wkn t
wk-[p] t = /-wk {t = t}

------------------------------------------------------------------------------
-- The sigma pairs of raw term and typing rule

<>-ty : ∀ {m} {Δ : Ctx m} → Σ (SubT m 0) ([] ▹ Δ ⊢_)
<>-ty = [] Σ., []

<,>-ty : ∀ {m n α} {Γ : Ctx m} {Δ : Ctx n} → Σ (SubT m n) (Δ ▹ Γ ⊢_) → Σ (Term m) (Γ ⊢_∈ α) →
         Σ (SubT m (suc n)) (Δ , α ▹ Γ ⊢_)
<,>-ty (ρ Σ., ⊢ρ) (t Σ., t∈) = ρ ∙ t Σ., ext t∈ ⊢ρ

∘-ty : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} →
       Σ (SubT n k) (Θ ▹ Γ ⊢_) → Σ (SubT m n) (Γ ▹ Δ ⊢_) → Σ (SubT m k) (Θ ▹ Δ ⊢_)
∘-ty (ρ Σ., ⊢ρ) (σ Σ., ⊢σ) = ρ ⋆ σ Σ., ⋆-preserv ⊢ρ ⊢σ             

sub-ty : ∀ {m n α} {Δ : Ctx m} {Γ : Ctx n} → Σ (Term n) (Γ ⊢_∈ α) →
         Σ (SubT m n) (Γ ▹ Δ ⊢_) → Σ (Term m) (Δ ⊢_∈ α)             
sub-ty (t Σ., t∈) (ρ Σ., ⊢ρ) = t [ ρ ] Σ., subst-lemma t∈ ⊢ρ

p-ty : ∀ {n α} {Γ : Ctx n} → Σ (SubT (suc n) n) (Γ ▹ Γ , α ⊢_)
p-ty = p Σ., p-preserv

q-ty : ∀ {n α} {Γ : Ctx n} → Σ (Term (suc n)) (Γ , α ⊢_∈ α)
q-ty = q Σ., ⊢vr0

ƛ-ty : ∀ {n} {Γ : Ctx n} {α β} → Σ (Term (suc n)) (Γ , α ⊢_∈ β) →
       Σ (Term n) (Γ ⊢_∈ (α ⇒ β))
ƛ-ty (t Σ., t∈) = ƛ t Σ., ƛ t∈       

app-ty : ∀ {n} {Γ : Ctx n} {α β} → Σ (Term n) (Γ ⊢_∈ (α ⇒ β)) →
         Σ (Term n) (Γ ⊢_∈ α) → Σ (Term n) (Γ ⊢_∈ β)
app-ty (t Σ., t∈) (u Σ., u∈) = t · u Σ., t∈ · u∈

