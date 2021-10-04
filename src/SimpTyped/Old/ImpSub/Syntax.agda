-------------------------------------------------------------------------------
-- Simply typed lambda calculus with variables as
-- membership witnesses
-------------------------------------------------------------------------------
module SimpTyped.Old.ImpSub.Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import SimpTyped.Old.Type
open import SimpTyped.Old.Context
open import Function as F using (_$_)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary hiding (_⇒_)
open import Data.List hiding ([_])
open P.≡-Reasoning

-------------------------------------------------------------------------------
-- Term syntax

infix 10 _·_

-- typed terms with variables as membership proofs

data Tm (Γ : Ctx) : Ty → Set where
  var : ∀ {α} (∈Γ : α ∈ Γ) → Tm Γ α
  _·_ : ∀ {α β} → Tm Γ (α ⇒ β) → Tm Γ α → Tm Γ β
  ƛ   : ∀ {α β} → Tm (Γ ∙ α) β → Tm Γ (α ⇒ β)

weaken : ∀ {α} {Γ Δ : Ctx} (φ : Γ ⊆ Δ) (t : Tm Γ α) → Tm Δ α
weaken φ (var ∈Γ) = var (sub-in φ ∈Γ)
weaken φ (t · u)  = weaken φ t · weaken φ u
weaken φ (ƛ t)    = ƛ (weaken (pop! φ) t)

q : ∀ {Γ α} → Tm (Γ ∙ α) α
q = var here

-- Substitutions of variables

_▸_ : (Δ Γ : Ctx) → Set
Δ ▸ ε       = ⊤
Δ ▸ (Γ ∙ α) = Δ ▸ Γ × α ∈ Δ

-- weakening variable substitutions

▸-weaken : ({Δ} {Θ} Γ : Ctx) (φ : Δ ⊆ Θ) (ρ : Δ ▸ Γ) → Θ ▸ Γ
▸-weaken ε       φ ρ       = tt
▸-weaken (Γ ∙ x) φ (ρ , t) = ▸-weaken Γ φ ρ , sub-in φ t

-- lookup for variables substs

tk∈ : ∀ {Γ Δ α} (∈Γ : α ∈ Γ) (ρ : Δ ▸ Γ) → α ∈ Δ
tk∈ {Γ ∙ x} here       (ρ , t) = t
tk∈ {Γ ∙ x} (there ∈Γ) (ρ , t) = tk∈ ∈Γ ρ

-- identity variable subst

idV : ∀ {Γ} → Γ ▸ Γ
idV {ε}     = tt
idV {Γ ∙ α} = ▸-weaken Γ ⊆-∙ idV , here

map-∈ : ∀ {Δ Γ α} (f : ∀ {α α'} → α ∈ Δ → α ∈ Δ ∙ α')
        → Δ ▸ Γ → (Δ ∙ α) ▸ Γ
map-∈ {Γ = ε}     f tt      = tt
map-∈ {Γ = Γ ∙ x} f (ρ , t) = map-∈ f ρ , f t

mapwk : ∀ {Γ Δ α x} (ρ : Δ ▸ Γ)
        → map-∈ {α = α} there (map-∈ {α = x} there ρ)
          ≡ map-∈ (there) (▸-weaken Γ (step ⊆-refl) ρ)
mapwk {ε} tt = refl
mapwk {Γ ∙ x} (ρ , t) = sym $ begin
  map-∈ (there) (▸-weaken Γ (step ⊆-refl) ρ) , there (there (sub-in ⊆-refl t))
    ≡⟨ cong (λ z → _ , there (there z)) (sub-in-refl t) ⟩
  map-∈ (there) (▸-weaken Γ (step ⊆-refl) ρ) , there (there t)
    ≡⟨ cong (_, there (there t)) (sym (mapwk ρ)) ⟩
  map-∈ (λ {α} → there) (map-∈ (λ {α} → there) ρ) , there (there t)
    ∎

map-tk∈ : ∀ {Γ Δ α} (f : ∀ {a b} → a ∈ Δ → a ∈ Δ ∙ b)
            (ρ : Δ ▸ Γ) (v : α ∈ Γ)
          → tk∈ v (map-∈ {α = α} f ρ) ≡ f (tk∈ v ρ)
map-tk∈ {Γ ∙ x} {Δ} f (ρ , t) here = refl
map-tk∈ {Γ ∙ x} {Δ} f (ρ , t) (there v) = map-tk∈ f ρ v

-- projection variable substitution

pV : ∀ {Γ α} → (Γ ∙ α) ▸ Γ
pV = map-∈ there idV

-- too much work for this triviality
postulate tk∈-pV-th : ∀ {Γ α} (v : α ∈ Γ) → tk∈ v (pV {α = α}) ≡ there v

-- Tm substitutions

Sub : (Δ Γ : Ctx) → Set
Sub Δ ε       = ⊤
Sub Δ (Γ ∙ t) = Sub Δ Γ × Tm Δ t

-- variable substitution to term

▸-to-sub : ∀ {Δ Γ} (f : ∀ {α} → α ∈ Δ → Tm Δ α) → Δ ▸ Γ → Sub Δ Γ
▸-to-sub {Γ = ε}     f tt      = tt
▸-to-sub {Γ = Γ ∙ x} f (ρ , t) = ▸-to-sub f ρ , f t

-- one version of projection substitution

p' : ∀ {Γ α} → Sub (Γ ∙ α) Γ
p' = ▸-to-sub var pV

-- weakening a substitution is mapping weaken on each term

wk-sub : ({Δ} {Θ} Γ : Ctx) (φ : Δ ⊆ Θ) (ρ : Sub Δ Γ) → Sub Θ Γ
wk-sub ε       φ ρ       = tt
wk-sub (Γ ∙ x) φ (ρ , t) = wk-sub Γ φ ρ , weaken φ t

wk : ∀ {Γ Δ α} → Sub Δ Γ → Sub (Δ ∙ α) Γ
wk ρ = wk-sub _ ⊆-∙ ρ

-- identity substitution

id : ∀ {Γ} → Sub Γ Γ
id {ε}     = tt
id {Γ ∙ α} = wk id , var here

-- lookup

tkVar : ∀ {Γ Δ α} (∈Γ : α ∈ Γ) (ρ : Sub Δ Γ) → Tm Δ α
tkVar here       (ρ , t) = t
tkVar (there ∈Γ) (ρ , t) = tkVar ∈Γ ρ

-- meta substitution operation

_[_] : ∀ {Γ Δ α} → Tm Γ α → Sub Δ Γ → Tm Δ α
var ∈Γ  [ ρ ] = tkVar ∈Γ ρ
(t · u) [ ρ ] = t [ ρ ] · u [ ρ ]
ƛ t     [ ρ ] = ƛ (t [ wk ρ , var here ])

-- traditional projection substitution

p : ∀ {Γ α} → Sub (Γ ∙ α) Γ
p {Γ} = wk-sub Γ ⊆-∙ id

weaken-same : ∀ {Γ α} (t : Tm Γ α) → Tm (Γ ∙ α) α
weaken-same = weaken ⊆-∙

infix 10 _∘_

-- composition of substitutions

_∘_ : ∀ {Γ Δ Θ} → Sub Γ Θ → Sub Δ Γ → Sub Δ Θ
_∘_ {Θ = ε}     ρ       σ = tt
_∘_ {Θ = Θ ∙ α} (ρ , t) σ = ρ ∘ σ , t [ σ ]

-- weakens a substitution and adds the last variable
-- ρ ∘ p is the same as mapping weaken on ρ;
-- this is directly a cwf combinator expression

↑_ : ∀ {Γ Δ α} → Sub Δ Γ → Sub (Δ ∙ α) (Γ ∙ α)
↑ ρ = ρ ∘ p , q 

simp : ∀ {Γ Δ Θ} (φ : Γ ⊆ Δ) (ρ : Sub Θ Δ) → Sub Θ Γ
simp base     ρ       = tt
simp (step φ) (ρ , t) = simp φ ρ
simp (pop! φ) (ρ , t) = simp φ ρ , t

-- congruences and inversion lemmas

cong-sub : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Sub Δ Γ} →
          t ≡ t' → γ ≡ γ' → t [ γ ] ≡ t' [ γ' ]
cong-sub refl refl = refl

cong-, : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Sub Γ Δ} →
         t ≡ t' → γ ≡ γ' → (γ , t) ≡ (γ' , t')
cong-, refl refl = refl

cong-∘ : ∀ {Γ Δ Θ} {γ δ : Sub Δ Θ} {γ' δ' : Sub Γ Δ} →
         γ ≡ δ → γ' ≡ δ' → γ ∘ γ' ≡ δ ∘ δ'
cong-∘ refl refl = refl             

var-eq : ∀ {Γ α} {φ₁ φ₂ : α ∈ Γ} → φ₁ ≡ φ₂ → var φ₁ ≡ var φ₂
var-eq refl = refl

var-eq-inv : ∀ {Γ α} {φ₁ φ₂ : α ∈ Γ} → var φ₁ ≡ var φ₂ → φ₁ ≡ φ₂
var-eq-inv refl = refl

ƛ-eq : ∀ {Γ α β} {t t' : Tm (Γ ∙ α) β} → t ≡ t' → ƛ t ≡ ƛ t'
ƛ-eq refl = refl

ƛ-eq-inv : ∀ {Γ α β} {t t' : Tm (Γ ∙ α) β} → ƛ t ≡ ƛ t' → t ≡ t'
ƛ-eq-inv refl = refl

app-eq : ∀ {Γ α β} {t t' : Tm Γ (α ⇒ β)} {u u' : Tm Γ α} →
          t ≡ t' → u ≡ u' → t · u ≡ t' · u'
app-eq refl refl = refl

app-eq-invl : ∀ {Γ α β} {t t' : Tm Γ (α ⇒ β)} {u u' : Tm Γ α} →
               t · u ≡ t' · u' → t ≡ t'
app-eq-invl refl = refl

app-eq-invr : ∀ {Γ α β} {t t' : Tm Γ (α ⇒ β)} {u u' : Tm Γ α} →
               t · u ≡ t' · u' → u ≡ u'
app-eq-invr refl = refl              
