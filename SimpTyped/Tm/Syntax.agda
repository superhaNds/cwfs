module SimpTyped.Tm.Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import SimpTyped.Type
open import SimpTyped.Context
open import Function using (_$_ ; _∘_)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary hiding (_⇒_)

infix 10 _·_
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

_▹_ : (Δ Γ : Ctx) → Set
Δ ▹ ε       = ⊤
Δ ▹ (Γ ∙ t) = (Term Δ t) × (Δ ▹ Γ)

▹-weaken : ({Δ} {Θ} Γ : Ctx) (φ : Δ ⊆ Θ) (ρ : Δ ▹ Γ) → Θ ▹ Γ
▹-weaken ε       φ ρ       = tt
▹-weaken (Γ ∙ x) φ (t , ρ) = weaken φ t , ▹-weaken Γ φ ρ

id : ∀ {Γ} → Γ ▹ Γ
id {ε}     = tt
id {Γ ∙ α} = var here , ▹-weaken Γ ⊆-∙ id

tkVar : ∀ {Γ Δ α} (∈Γ : α ∈ Γ) (ρ : Δ ▹ Γ) → Term Δ α
tkVar here       (t , ρ) = t
tkVar (there ∈Γ) (t , ρ) = tkVar ∈Γ ρ

_[_] : ∀ {Γ Δ α} → Term Γ α → Δ ▹ Γ → Term Δ α
var ∈Γ [ ρ ]  = tkVar ∈Γ ρ
(t · u) [ ρ ] = t [ ρ ] · u [ ρ ]
ƛ t [ ρ ]     = ƛ (t [ var here , ▹-weaken _ ⊆-∙ ρ ])

p : ∀ {Γ α} → (Γ ∙ α) ▹ Γ
p {Γ} = ▹-weaken Γ ⊆-∙ id

weaken-same : ∀ {Γ α β} (t : Term Γ α) → Term (Γ ∙ β) α
weaken-same = _[ p ]

p' : ∀ {Γ α} → (Γ ∙ α) ▹ Γ
p' = proj₂ id

infix 10 _⋆_

_⋆_ : ∀ {Γ Δ Θ} → Γ ▹ Θ → Δ ▹ Γ → Δ ▹ Θ
_⋆_ {Θ = ε}     ρ       σ = tt
_⋆_ {Θ = Θ ∙ α} (t , ρ) σ = t [ σ ] , ρ ⋆ σ  

↑_ : ∀ {Γ Δ α} → Δ ▹ Γ → (Δ ∙ α) ▹ (Γ ∙ α)
↑ ρ = var here , ρ ⋆ p

simp : ∀ {Γ Δ Θ} (φ : Γ ⊆ Δ) (ρ : Θ ▹ Δ) → Θ ▹ Γ
simp base     ρ       = tt
simp (step φ) (t , ρ) = simp φ ρ
simp (pop! φ) (t , ρ) = t , simp φ ρ

cong-[] : ∀ {Γ Δ α} {t t' : Term Γ α} {γ γ' : Δ ▹ Γ} →
          t ≡ t' → γ ≡ γ' → t [ γ ] ≡ t' [ γ' ]
cong-[] refl refl = refl

cong-, : ∀ {Γ Δ α} {t t' : Term Γ α} {γ γ' : Γ ▹ Δ} →
         t ≡ t' → γ ≡ γ' → (t , γ) ≡ (t' , γ')
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
