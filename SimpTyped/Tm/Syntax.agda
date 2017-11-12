module SimpTyped.Tm.Syntax where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import SimpTyped.Tm.Type
open import SimpTyped.Tm.Context
open import Function using (_$_ ; _∘_)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)

Ctx : Set
Ctx = Ctxt Ty

data Term (Γ : Ctx) : Ty → Set where
  var : ∀ {α} (∈Γ : α ∈ Γ) → Term Γ α
  --_·_ : ∀ {α β} → Term Γ (α ⇒ β) → Term Γ α → Term Γ β
  --ƛ   : ∀ α {β} → Term (Γ , α) β → Term Γ α → Term Γ (α ⇒ β)

weaken : ∀ {α} {Γ Δ : Ctx} (φ : Γ ⊆ Δ) (t : Term Γ α) → Term Δ α
weaken φ (var ∈Γ) = var (sub-in φ ∈Γ)

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
tkVar here (t , ρ)       = t
tkVar (there ∈Γ) (t , ρ) = tkVar ∈Γ ρ

_[_] : ∀ {Γ Δ α} → Term Γ α → Δ ▹ Γ → Term Δ α
var ∈Γ [ ρ ] = tkVar ∈Γ ρ

p : ∀ {Γ α} → (Γ ∙ α) ▹ Γ
p {Γ} = ▹-weaken Γ ⊆-∙ id

p' : ∀ {Γ α} → (Γ ∙ α) ▹ Γ
p' {Γ} {α} = proj₂ id

infix 20 _⋆_

_⋆_ : ∀ {Γ Δ Θ} → Γ ▹ Θ → Δ ▹ Γ → Δ ▹ Θ
_⋆_ {Θ = ε}     ρ       σ = tt
_⋆_ {Θ = Θ ∙ α} (t , ρ) σ = t [ σ ] , ρ ⋆ σ  

simp : ∀ {Γ Δ Θ} (φ : Γ ⊆ Δ) (ρ : Θ ▹ Δ) → Θ ▹ Γ
simp base     ρ       = tt
simp (step φ) (t , ρ) = simp φ ρ
simp (pop! φ) (t , ρ) = t , simp φ ρ

infix 6 _~_
data _~_ {Γ α} : (t₁ t₂ : Term Γ α) → Set where
  varcong : (φ : α ∈ Γ) → var φ ~ var φ
  sym~ : ∀ {t t'} → t ~ t' → t' ~ t
  trans~ : ∀ {t₁ t₂ t₃} → t₁ ~ t₂ → t₂ ~ t₃ → t₂ ~ t₃

refl~ : ∀ {Γ α} {t : Term Γ α} → t ~ t
refl~ {t = var ∈Γ} = varcong ∈Γ

cong-[] : ∀ {Γ Δ α} {t t' : Term Γ α} {γ γ' : Δ ▹ Γ} →
          t ~ t' → γ ≡ γ' → t [ γ ] ~ t' [ γ' ]
cong-[] (varcong φ) refl = refl~
cong-[] (sym~ t~t') refl = sym~ (cong-[] t~t' refl)
cong-[] (trans~ t~t' t~t'') refl = trans~ (cong-[] t~t' refl) (cong-[] t~t'' refl)

cong-, : ∀ {Γ Δ α} {t t' : Term Γ α} {γ γ' : Γ ▹ Δ} →
         t ~ t' → γ ≡ γ' → (t , γ) ≡ (t' , γ')
cong-, (varcong φ) refl = refl
cong-, (sym~ t~t') refl = sym (cong-, t~t' refl)
cong-, (trans~ t~t' t~t'') refl = cong-, t~t'' refl

cong-⋆ : ∀ {Γ Δ Θ} {γ δ : Δ ▹ Θ} {γ' δ' : Γ ▹ Δ} →
         γ ≡ δ → γ' ≡ δ' → γ ⋆ γ' ≡ δ ⋆ δ'
cong-⋆ refl refl = refl             

var-eq : ∀ {Γ α} {φ₁ φ₂ : α ∈ Γ} → φ₁ ≡ φ₂ → var φ₁ ≡ var φ₂
var-eq refl = refl

var-eq-inv : ∀ {Γ α} {φ₁ φ₂ : α ∈ Γ} → var φ₁ ≡ var φ₂ → φ₁ ≡ φ₂
var-eq-inv refl = refl

wk-refl : ∀ {Γ α} (t : Term Γ α) → weaken ⊆-refl t ≡ t
wk-refl (var ∈Γ) = cong var (sub-in-refl ∈Γ)

wk-sub-refl : ∀ {Δ} Γ (ρ : Δ ▹ Γ) → ▹-weaken Γ (⊆-refl) ρ ≡ ρ
wk-sub-refl ε tt            = refl
wk-sub-refl (Γ ∙ x) (t , ρ) = cong₂ _,_ (wk-refl t) (wk-sub-refl Γ ρ)

id=<pq> : ∀ {Γ α} → id {Γ ∙ α} ≡ (q , p)
id=<pq> {ε}     = refl
id=<pq> {Γ ∙ x} = refl

[] : ∀ {Γ} → Γ ▹ ε
[] = tt

∘-<> : ∀ {Γ Δ} (ρ : Γ ▹ Δ) → [] {Γ} ⋆ ρ ≡ [] {Γ}
∘-<> _ = refl

q[] : ∀ {Γ Δ α} (t : Term Γ α) (ρ : Γ ▹ Δ) → q [ t , ρ ] ~ t
q[] t ρ = refl~

tk-weaken : ∀ {Γ Δ Θ α} (φ : α ∈ Γ) (i : Δ ⊆ Θ) (ρ : Δ ▹ Γ) →
            weaken i (tkVar φ ρ) ~ tkVar φ (▹-weaken Γ i ρ)
tk-weaken here i ρ = refl~
tk-weaken (there φ) i (t , ρ) = tk-weaken φ i ρ            

simp-refl : ∀ (Γ {Δ} : Ctx) (ρ : Δ ▹ Γ) → simp ⊆-refl ρ ≡ ρ
simp-refl ε tt = refl
simp-refl (Γ ∙ x) (t , ρ) = cong (t ,_) (simp-refl Γ ρ)

[]-wk : ∀ {Γ Δ N α} (φ : Δ ⊆ N) (t : Term Γ α) (ρ : Δ ▹ Γ) →
        weaken φ (t [ ρ ]) ~ t [ ▹-weaken Γ φ ρ ]
[]-wk φ (var ∈Γ) ρ = tk-weaken ∈Γ φ ρ      

wk-⋆ : ∀ (Γ {Δ} {E} {Θ} : Ctx) (φ : E ⊆ Θ) (ρ : Δ ▹ Γ) (σ : E ▹ Δ) →
       ρ ⋆ (▹-weaken Δ φ σ) ≡ ▹-weaken Γ φ (ρ ⋆ σ)
wk-⋆ ε φ ρ σ = refl
wk-⋆ (Γ ∙ x) φ (t , ρ) σ = cong-, (sym~ ([]-wk φ t σ)) (wk-⋆ Γ φ ρ σ)

tk-⋆ : ∀ {Γ Δ Θ α} (φ : α ∈ Γ) (ρ : Δ ▹ Γ) (σ : Θ ▹ Δ) →
       (tkVar φ ρ) [ σ ] ~ tkVar φ (ρ ⋆ σ)
tk-⋆ here ρ σ = refl~
tk-⋆ (there φ) (t , ρ) σ = tk-⋆ φ ρ σ

tk-in : ∀ {Γ Δ Θ α} (φ : Γ ⊆ Δ) (v : α ∈ Γ) (ρ : Θ ▹ Δ) →
        tkVar (sub-in φ v) ρ ≡ tkVar v (simp φ ρ)
tk-in (step φ) here      (t , ρ) = tk-in φ here ρ
tk-in (step φ) (there v) (t , ρ) = tk-in φ (there v) ρ
tk-in (pop! φ) here      _       = refl
tk-in (pop! φ) (there v) (t , ρ) = tk-in φ v ρ

wk-[] : ∀ {Γ Δ Θ α} (v : Γ ⊆ Δ) (t : Term Γ α) (ρ : Θ ▹ Δ) →
        (weaken v t) [ ρ ] ≡ t [ simp v ρ ]
wk-[] v (var ∈Γ) ρ = tk-in v ∈Γ ρ

⋆-step : ∀ Γ {Δ} {Θ} {α} → (ρ : Δ ▹ Γ) (σ : Θ ▹ Δ) (t : Term Θ α) →
        (▹-weaken Γ ⊆-∙ ρ) ⋆ (t , σ) ≡ ρ ⋆ σ
⋆-step ε ρ σ t = refl
⋆-step (Γ ∙ x) (u , ρ) σ t =
  cong₂ _,_ (trans (wk-[] (step ⊆-refl) u (t , σ))
                   (cong (u [_]) (simp-refl _ σ)))
            (⋆-step Γ ρ σ t) 

tkVar-id : ∀ {Γ α} (φ : α ∈ Γ) → tkVar φ id ≡ var φ
tkVar-id here = refl
tkVar-id {Γ = Γ ∙ x} (there φ) = {!!}

t[id] : ∀ {Γ α} (t : Term Γ α) → t [ id ] ≡ t
t[id] (var ∈Γ) = tkVar-id ∈Γ

idR : ∀ {Γ Δ} (ρ : Γ ▹ Δ) → ρ ⋆ id ≡ ρ
idR {Δ = ε}     tt      = refl
idR {Δ = Δ ∙ x} (t , ρ) =
  trans (cong (t [ id ] ,_) (idR ρ))
        (cong (_, ρ) (t[id] t))

p⋆, : ∀ {Δ Θ α} (t : Term Δ α) (γ : Δ ▹ Θ) → p ⋆ (t , γ) ≡ γ

idL : ∀ {Γ Δ} (ρ : Δ ▹ Γ) → id ⋆ ρ ≡ ρ

p⋆, {Θ = Θ} t = trans (⋆-step Θ id _ t) ∘ idL

idL {ε}     tt      = refl
idL {Γ ∙ α} (t , ρ) = cong (t ,_) (p⋆, t ρ)

[]-asso : ∀ {Γ Δ Θ α} (t : Term Δ α) (γ : Γ ▹ Δ) (δ : Θ ▹ Γ) →
          t [ γ ⋆ δ ] ≡ t [ γ ] [ δ ]
[]-asso {Δ = Δ ∙ α} (var here) γ δ = refl
[]-asso {Δ = Δ ∙ α} (var (there ∈Γ)) (u , γ) δ = []-asso (var ∈Γ) γ δ            

[]-asso~ : ∀ {Γ Δ Θ α} (t : Term Δ α) (γ : Γ ▹ Δ) (δ : Θ ▹ Γ) →
          t [ γ ⋆ δ ] ~ t [ γ ] [ δ ]
[]-asso~ {Δ = Δ ∙ α} (var here) γ δ = refl~
[]-asso~ {Δ = Δ ∙ α} (var (there ∈Γ)) (u , γ) δ = []-asso~ (var ∈Γ) γ δ            

⋆-asso : ∀ {Γ Δ Θ Λ} (γ : Δ ▹ Θ) (δ : Γ ▹ Δ) (ζ : Λ ▹ Γ) →
         (γ ⋆ δ) ⋆ ζ ≡ γ ⋆ (δ ⋆ ζ)
⋆-asso {Θ = ε} γ δ ζ = refl
⋆-asso {Θ = Θ ∙ _} (t , γ) δ ζ =
  trans (cong (_, (γ ⋆ δ) ⋆ ζ) (sym ([]-asso t δ ζ)))
        (cong (t [ δ ⋆ ζ ] ,_) (⋆-asso γ δ ζ))
