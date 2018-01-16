-------------------------------------------------------------------------
-- Simply typed lambda calculus based on raw terms with a typing relation
-- for terms and substitutions. Proof that types are preserved and thus
-- STLC is a simply typed cwf.
-------------------------------------------------------------------------
module Ext-Typed.STyped.Preservation where

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
open import Ext-Typed.Syntax
open import Ext-Typed.Raw
open ≡-Reasoning

-------------------------------------------------------------------------
-- Types

infixr 20 _⇒_

data Ty : Set where
  ♭   : Ty
  _⇒_ : Ty → Ty → Ty

-- Contexts

Ctx : Nat → Set
Ctx = Vec.Vec Ty

_,_ : ∀ {n} (Γ : Ctx n) (α : Ty) → Ctx (suc n)
Γ , α = α ∷ Γ

-- Typing rules for terms

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctx n) : Term n → Ty → Set where

  var : ∀ {i} →

          ------------------------
           Γ ⊢ var i ∈ lookup i Γ
  
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

open TermSubst tmSubst hiding (var)

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

id' : ∀ {n} → SubT n n
id' = id

-- Well-typed substitutions

infix  4 _▹_⊢_

data _▹_⊢_ {n} : ∀ {m} → Ctx m → Ctx n → SubT n m → Set where

  []  : ∀ {Δ} → [] ▹ Δ ⊢ []
  
  ext : ∀ {m} {Γ : Ctx m} {Δ σ t ρ} →
  
          Δ ⊢ t ∈ σ → Γ ▹ Δ ⊢ ρ →
          -----------------------
             Γ , σ ▹ Δ ⊢ ρ ∙ t

--------------------------------------------------------------------------------
-- Typing rules for scwf, i.e., types are preserved for each operator 

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
                Γ ⊢ t ∈ α →
                Γ ▹ Δ ⊢ Vec.map var ρ →
                Δ ⊢ t /Var ρ ∈ α
  []-preserv (var {i}) ⊢ρ = lookup-preserv i _ ⊢ρ
  []-preserv (ƛ t)     ⊢ρ = ƛ ([]-preserv t (↑-preserv ⊢ρ))
  []-preserv (t · u)   ⊢ρ = []-preserv t ⊢ρ · []-preserv u ⊢ρ

weaken-preserv : ∀ {n Γ α β} {t : Term n} →
                  Γ ⊢ t ∈ β →
                  Γ , α ⊢ weaken t ∈ β
weaken-preserv t = Var.[]-preserv t Var.wk-preserv

map-weaken-preserv : ∀ {m n Γ Δ α} {ρ : Sub Term m n} →
                      Γ ▹ Δ ⊢ ρ →
                      Γ ▹ Δ , α ⊢ Vec.map weaken ρ
map-weaken-preserv []         = []
map-weaken-preserv (ext t ⊢ρ) =
  ext (weaken-preserv t) (map-weaken-preserv ⊢ρ)

↑-preserv : ∀ {m n Γ Δ α} {ρ : Sub Term m n} →
             Γ ▹ Δ ⊢ ρ →
             Γ , α ▹ Δ , α ⊢ ρ ↑
↑-preserv ⊢ρ = ext var (map-weaken-preserv ⊢ρ)

-- identity preserves

id-preserv : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ id
id-preserv {Γ = []}    = []
id-preserv {Γ = _ ∷ _} = ↑-preserv id-preserv

-- projection preserves

p-preserv : ∀ {n α} {Γ : Ctx n} → Γ ▹ Γ , α ⊢ p
p-preserv {Γ = []}    = []
p-preserv {Γ = _ ∷ Γ} = map-weaken-preserv $ ↑-preserv id-preserv

-- lookup preserves

lookup-preserv : ∀ {m n} {Γ : Ctx m}
                   {Δ : Ctx n} i {ρ} →
                  Γ ▹ Δ ⊢ ρ →
                  Δ ⊢ lookup i ρ ∈ lookup i Γ
lookup-preserv zero    (ext t ⊢ρ) = t
lookup-preserv (suc x) (ext t ⊢ρ) = lookup-preserv x ⊢ρ

-- substitution preserves

subst-lemma : ∀ {m n} {Γ : Ctx m}
                {Δ : Ctx n} {α t ρ} →
               Γ ⊢ t ∈ α →
               Γ ▹ Δ ⊢ ρ →
               Δ ⊢ t [ ρ ] ∈ α                 
subst-lemma (var {i}) ⊢ρ = lookup-preserv i ⊢ρ
subst-lemma (ƛ t)     ⊢ρ = ƛ (subst-lemma t (↑-preserv ⊢ρ))
subst-lemma (t · u)   ⊢ρ = subst-lemma t ⊢ρ · subst-lemma u ⊢ρ

-- cons preserves

∙-preserv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
              {t : Term n} {ρ : Sub Term m n} {α} →
             Γ ⊢ t ∈ α →
             Δ ▹ Γ ⊢ ρ →
             Δ , α ▹ Γ ⊢ ρ ∙ t
∙-preserv t ⊢ρ = ext t ⊢ρ

-- composition preserves

⋆-preserv : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
              {ρ : SubT n k} {σ : SubT m n} →
             Θ ▹ Γ ⊢ ρ →
             Γ ▹ Δ ⊢ σ →
             Θ ▹ Δ ⊢ ρ ⋆ σ
⋆-preserv []         _   = []
⋆-preserv (ext x ⊢ρ) ⊢ρ' =
  ∙-preserv (subst-lemma x ⊢ρ')
            (⋆-preserv ⊢ρ ⊢ρ')

open TermLemmas tmLemmas public hiding (var)

wk-[p] : ∀ {n} (t : Term n) → t [ p ] ≡ wkn t
wk-[p] t = /-wk {t = t}

-------------------------------------------------------------------------
-- The sigma pairs of raw term and corresponding typing rule

-- empty substitution

<>-ty : ∀ {m} {Δ : Ctx m} → Σ (SubT m 0) ([] ▹ Δ ⊢_)
<>-ty = [] Σ., []

-- extending a substitution

<,>-ty : ∀ {m n α} {Γ : Ctx m} {Δ : Ctx n} → Σ (SubT m n) (Δ ▹ Γ ⊢_) → Σ (Term m) (Γ ⊢_∈ α) →
         Σ (SubT m (suc n)) (Δ , α ▹ Γ ⊢_)
<,>-ty (ρ Σ., ⊢ρ) (t Σ., t∈) = ρ ∙ t Σ., ext t∈ ⊢ρ

-- composition

∘-ty : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} →
       Σ (SubT n k) (Θ ▹ Γ ⊢_) → Σ (SubT m n) (Γ ▹ Δ ⊢_) → Σ (SubT m k) (Θ ▹ Δ ⊢_)
∘-ty (ρ Σ., ⊢ρ) (σ Σ., ⊢σ) = ρ ⋆ σ Σ., ⋆-preserv ⊢ρ ⊢σ             

-- substitution operation

sub-ty : ∀ {m n α} {Δ : Ctx m} {Γ : Ctx n} → Σ (Term n) (Γ ⊢_∈ α) →
         Σ (SubT m n) (Γ ▹ Δ ⊢_) → Σ (Term m) (Δ ⊢_∈ α)             
sub-ty (t Σ., t∈) (ρ Σ., ⊢ρ) = t [ ρ ] Σ., subst-lemma t∈ ⊢ρ

-- identity

id-ty : ∀ {n} {Γ : Ctx n} → Σ (SubT n n) (Γ ▹ Γ ⊢_)
id-ty = id' Σ., id-preserv

-- lifting/projection

p-ty : ∀ {n α} {Γ : Ctx n} → Σ (SubT (suc n) n) (Γ ▹ Γ , α ⊢_)
p-ty = p Σ., p-preserv

-- zeroth variable

q-ty : ∀ {n α} {Γ : Ctx n} → Σ (Term (suc n)) (Γ , α ⊢_∈ α)
q-ty = q Σ., ⊢vr0

-- lambda abstraction

ƛ-ty : ∀ {n} {Γ : Ctx n} {α β} → Σ (Term (suc n)) (Γ , α ⊢_∈ β) →
       Σ (Term n) (Γ ⊢_∈ (α ⇒ β))
ƛ-ty (t Σ., t∈) = ƛ t Σ., ƛ t∈       

-- apply

app-ty : ∀ {n} {Γ : Ctx n} {α β} → Σ (Term n) (Γ ⊢_∈ (α ⇒ β)) →
         Σ (Term n) (Γ ⊢_∈ α) → Σ (Term n) (Γ ⊢_∈ β)
app-ty (t Σ., t∈) (u Σ., u∈) = t · u Σ., t∈ · u∈
