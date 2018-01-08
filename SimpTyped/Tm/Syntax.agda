-------------------------------------------------------------------------------
-- Simply typed lambda calculus with variables as
-- membership witnesses
-------------------------------------------------------------------------------
module SimpTyped.Tm.Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import SimpTyped.Type
open import SimpTyped.Context
open import Function using (_$_ ; _∘_)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary hiding (_⇒_)
open import Data.List hiding ([_])
open P.≡-Reasoning

-------------------------------------------------------------------------------
-- Term syntax

infix 10 _·_

-- typed terms with variables as membership proofs

data Term (Γ : Ctx) : Ty → Set where
  var : ∀ {α} (∈Γ : α ∈ Γ) → Term Γ α
  _·_ : ∀ {α β} → Term Γ (α ⇒ β) → Term Γ α → Term Γ β
  ƛ   : ∀ {α β} → Term (Γ ∙ α) β → Term Γ (α ⇒ β)

weaken : ∀ {α} {Γ Δ : Ctx} (φ : Γ ⊆ Δ) (t : Term Γ α) → Term Δ α
weaken φ (var ∈Γ) = var (sub-in φ ∈Γ)
weaken φ (t · u)  = weaken φ t · weaken φ u
weaken φ (ƛ t)    = ƛ (weaken (pop! φ) t)

q : ∀ {Γ α} → Term (Γ ∙ α) α
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

map-∈ : ∀ {Δ Γ α} (f : ∀ {α α'} → α ∈ Δ → α ∈ Δ ∙ α') →
        Δ ▸ Γ → (Δ ∙ α) ▸ Γ
map-∈ {Γ = ε}     f tt      = tt
map-∈ {Γ = Γ ∙ x} f (ρ , t) = map-∈ f ρ , f t

mapwk : ∀ {Γ Δ α x} (ρ : Δ ▸ Γ) → map-∈ {α = α} there (map-∈ {α = x} there ρ) ≡
                                  map-∈ (there) (▸-weaken Γ (step ⊆-refl) ρ)
mapwk {ε} tt = refl
mapwk {Γ ∙ x} (ρ , t) = sym $ begin
  map-∈ (there) (▸-weaken Γ (step ⊆-refl) ρ) , there (there (sub-in ⊆-refl t))
    ≡⟨ cong (λ z → _ , there (there z)) (sub-in-refl t) ⟩
  map-∈ (there) (▸-weaken Γ (step ⊆-refl) ρ) , there (there t)
    ≡⟨ cong (_, there (there t)) (sym (mapwk ρ)) ⟩
  map-∈ (λ {α} → there) (map-∈ (λ {α} → there) ρ) , there (there t)
    ∎

map-tk∈ : ∀ {Γ Δ α} (f : ∀ {a b} → a ∈ Δ → a ∈ Δ ∙ b) (ρ : Δ ▸ Γ) (v : α ∈ Γ) →
           tk∈ v (map-∈ {α = α} f ρ) ≡ f (tk∈ v ρ)
map-tk∈ {Γ ∙ x} {Δ} f (ρ , t) here = refl
map-tk∈ {Γ ∙ x} {Δ} f (ρ , t) (there v) = map-tk∈ f ρ v

-- projection variable substitution

pV : ∀ {Γ α} → (Γ ∙ α) ▸ Γ
pV = map-∈ there idV

-- too much work for this triviality
postulate tk∈-pV-th : ∀ {Γ α} (v : α ∈ Γ) → tk∈ v (pV {α = α}) ≡ there v

-- Term substitutions

_▹_ : (Δ Γ : Ctx) → Set
Δ ▹ ε       = ⊤
Δ ▹ (Γ ∙ t) = Δ ▹ Γ × Term Δ t

-- variable substitution to term

▸-to-▹ : ∀ {Δ Γ} (f : ∀ {α} → α ∈ Δ → Term Δ α) → Δ ▸ Γ → Δ ▹ Γ
▸-to-▹ {Γ = ε}     f tt      = tt
▸-to-▹ {Γ = Γ ∙ x} f (ρ , t) = ▸-to-▹ f ρ , f t

-- one version of projection substitution

p' : ∀ {Γ α} → (Γ ∙ α) ▹ Γ
p' = ▸-to-▹ var pV

-- weakening a substitution is mapping weaken on each term

▹-weaken : ({Δ} {Θ} Γ : Ctx) (φ : Δ ⊆ Θ) (ρ : Δ ▹ Γ) → Θ ▹ Γ
▹-weaken ε       φ ρ       = tt
▹-weaken (Γ ∙ x) φ (ρ , t) = ▹-weaken Γ φ ρ , weaken φ t

-- identity substitution

id : ∀ {Γ} → Γ ▹ Γ
id {ε}     = tt
id {Γ ∙ α} = ▹-weaken Γ ⊆-∙ id , var here

-- lookup

tkVar : ∀ {Γ Δ α} (∈Γ : α ∈ Γ) (ρ : Δ ▹ Γ) → Term Δ α
tkVar here       (ρ , t) = t
tkVar (there ∈Γ) (ρ , t) = tkVar ∈Γ ρ

-- meta substitution operation

_[_] : ∀ {Γ Δ α} → Term Γ α → Δ ▹ Γ → Term Δ α
var ∈Γ [ ρ ]  = tkVar ∈Γ ρ
(t · u) [ ρ ] = t [ ρ ] · u [ ρ ]
ƛ t [ ρ ]     = ƛ (t [ ▹-weaken _ ⊆-∙ ρ , var here ])

-- traditional projection substitution

p : ∀ {Γ α} → (Γ ∙ α) ▹ Γ
p {Γ} = ▹-weaken Γ ⊆-∙ id

weaken-same : ∀ {Γ α} (t : Term Γ α) → Term (Γ ∙ α) α
weaken-same = weaken ⊆-∙

infix 10 _⋆_

-- composition of substitutions

_⋆_ : ∀ {Γ Δ Θ} → Γ ▹ Θ → Δ ▹ Γ → Δ ▹ Θ
_⋆_ {Θ = ε}     ρ       σ = tt
_⋆_ {Θ = Θ ∙ α} (ρ , t) σ = ρ ⋆ σ , t [ σ ]

-- weakens a substitution and adds the last variable
-- ρ ⋆ p is the same as mapping weaken on ρ; this is a proven property is Properties

↑_ : ∀ {Γ Δ α} → Δ ▹ Γ → (Δ ∙ α) ▹ (Γ ∙ α)
↑ ρ = ρ ⋆ p , var here 

simp : ∀ {Γ Δ Θ} (φ : Γ ⊆ Δ) (ρ : Θ ▹ Δ) → Θ ▹ Γ
simp base     ρ       = tt
simp (step φ) (ρ , t) = simp φ ρ
simp (pop! φ) (ρ , t) = simp φ ρ , t

-- congruences and inversion lemmas

cong-[] : ∀ {Γ Δ α} {t t' : Term Γ α} {γ γ' : Δ ▹ Γ} →
          t ≡ t' → γ ≡ γ' → t [ γ ] ≡ t' [ γ' ]
cong-[] refl refl = refl

cong-, : ∀ {Γ Δ α} {t t' : Term Γ α} {γ γ' : Γ ▹ Δ} →
         t ≡ t' → γ ≡ γ' → (γ , t) ≡ (γ' , t')
cong-, refl refl = refl

cong-⋆ : ∀ {Γ Δ Θ} {γ δ : Δ ▹ Θ} {γ' δ' : Γ ▹ Δ} →
         γ ≡ δ → γ' ≡ δ' → γ ⋆ γ' ≡ δ ⋆ δ'
cong-⋆ refl refl = refl             

var-eq : ∀ {Γ α} {φ₁ φ₂ : α ∈ Γ} → φ₁ ≡ φ₂ → var φ₁ ≡ var φ₂
var-eq refl = refl

var-eq-inv : ∀ {Γ α} {φ₁ φ₂ : α ∈ Γ} → var φ₁ ≡ var φ₂ → φ₁ ≡ φ₂
var-eq-inv refl = refl

ƛ-eq : ∀ {Γ α β} {t t' : Term (Γ ∙ α) β} → t ≡ t' → ƛ t ≡ ƛ t'
ƛ-eq refl = refl

ƛ-eq-inv : ∀ {Γ α β} {t t' : Term (Γ ∙ α) β} → ƛ t ≡ ƛ t' → t ≡ t'
ƛ-eq-inv refl = refl

app-eq : ∀ {Γ α β} {t t' : Term Γ (α ⇒ β)} {u u' : Term Γ α} →
          t ≡ t' → u ≡ u' → t · u ≡ t' · u'
app-eq refl refl = refl

app-eq-invl : ∀ {Γ α β} {t t' : Term Γ (α ⇒ β)} {u u' : Term Γ α} →
              t · u ≡ t' · u' → t ≡ t'
app-eq-invl refl = refl

app-eq-invr : ∀ {Γ α β} {t t' : Term Γ (α ⇒ β)} {u u' : Term Γ α} →
              t · u ≡ t' · u' → u ≡ u'
app-eq-invr refl = refl              
