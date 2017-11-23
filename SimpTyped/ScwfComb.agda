module SimpTyped.ScwfComb where

open import Data.Nat renaming (ℕ to Nat)
open import Data.List hiding ([_])
open import Data.Fin
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (IsEquivalence ; Setoid)
import Relation.Binary.EqReasoning as EqR
open import SimpTyped.Context renaming (_∙_ to _,_)
open import SimpTyped.Type

data Tm : Ctx → Ty → Set
data Hom : Ctx → Ctx → Set

data Tm where
  q    : ∀ {Γ α}   → Tm (Γ , α) α
  _[_] : ∀ {Γ Δ α} → Tm Γ α  → Hom Δ Γ → Tm Δ α
  lam  : ∀ {Γ α β} → Tm (Γ , α) β → Tm Γ (α ⇒ β)
  app  : ∀ {Γ α β} → Tm Γ (α ⇒ β) → Tm Γ α → Tm Γ β

data Hom where
  <>    : ∀ {Γ} → Hom Γ ε
  id    : ∀ {Γ} → Hom Γ Γ
  p     : ∀ {Γ α} → Hom (Γ , α) Γ
  _∘_   : ∀ {Γ Δ Θ} → Hom Γ Θ → Hom Δ Γ → Hom Δ Θ
  <_,_> : ∀ {Γ Δ α} → Hom Γ Δ → Tm Γ α  → Hom Γ (Δ , α)

weaken-same : ∀ {Γ α} → Tm Γ α → Tm (Γ , α) α
weaken-same = _[ p ]

varCwf : ∀ {Γ α} → (α ∈ Γ) → Tm Γ α
varCwf here      = q
varCwf (there φ) = varCwf φ [ p ]

infix 6 _~_
infix 6 _~~_

data _~_  : ∀ {Γ α} (t₁ t₂ : Tm Γ α) → Set
data _~~_ : ∀ {Γ Δ} (γ₁ γ₂ : Hom Γ Δ) → Set

data _~_ where
  tmId    : ∀ {Γ α} (t : Tm Γ α) → t [ id ] ~ t
  q[]     : ∀ {Γ Δ α} (t : Tm Γ α) (γ : Hom Γ Δ) → q [ < γ , t > ] ~ t
  clos    : ∀ {Γ Δ Θ α} (t : Tm Δ α) (γ : Hom Γ Δ) (δ : Hom Θ Γ) →
            t [ γ ∘ δ ] ~ t [ γ ] [ δ ]
  appCm   : ∀ {Γ Δ α β} (t : Tm Γ (α ⇒ β)) (u : Tm Γ α) (γ : Hom Δ Γ) →
            app (t [ γ ]) (u [ γ ]) ~ app t u [ γ ]
  lamCm   : ∀ {Γ Δ α β} (t : Tm (Γ , α) β) (γ : Hom Δ Γ) →
            lam t [ γ ] ~ lam (t [ < γ ∘ p , q > ])
  cong-[] : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Hom Δ Γ} →
            t ~ t' → γ ~~ γ' → t [ γ ] ~ t' [ γ' ]
  cong-app  : ∀ {Γ α β} {t t' : Tm Γ (α ⇒ β)} {u u' : Tm Γ α} →
            t ~ t' → u ~ u' → app t u ~ app t' u'
  cong-lam : ∀ {Γ α β} {t t' : Tm (Γ , α) β} → t ~ t' → lam t ~ lam t'
  sym~    : ∀ {Γ α} {t t' : Tm Γ α} → t ~ t' → t' ~ t
  trans~  : ∀ {Γ α} {t t' t'' : Tm Γ α} → t ~ t' → t' ~ t'' → t ~ t''

data _~~_ where
  id₀      : id {ε} ~~ <>
  ∘<>      : ∀ {Γ Δ} (γ : Hom Γ Δ) → <> ∘ γ ~~ <>
  varp     : ∀ {Γ α} → id {Γ , α} ~~ < p , q > 
  idL      : ∀ {Γ Δ} (γ : Hom Δ Γ) → id ∘ γ ~~ γ
  idR      : ∀ {Γ Δ} (γ : Hom Γ Δ) → γ ∘ id ~~ γ
  assoc    : ∀ {Γ Δ Θ Λ} (γ : Hom Δ Θ) (δ : Hom Γ Δ) (ζ : Hom Λ Γ) →
             (γ ∘ δ) ∘ ζ ~~ γ ∘ (δ ∘ ζ)
  pCons    : ∀ {Δ Θ α} (t : Tm Δ α) (γ : Hom Δ Θ) → p ∘ < γ , t > ~~ γ
  maps     : ∀ {Γ Δ Θ α} (t : Tm Δ α) (γ : Hom Δ Θ) (δ : Hom Γ Δ) →
             < γ , t > ∘ δ ~~ < γ ∘ δ , t [ δ ] >
  cong-<,> : ∀ {Γ Δ α} {t t' : Tm Γ α} {γ γ' : Hom Γ Δ} →
             t ~ t' → γ ~~ γ' → < γ , t > ~~ < γ' , t' >
  cong-∘   : ∀ {Γ Δ Θ} {γ δ : Hom Δ Θ} {γ' δ' : Hom Γ Δ} →
             γ ~~ δ → γ' ~~ δ' → γ ∘ γ' ~~ δ ∘ δ'
  sym~~    : ∀ {Γ Δ} {γ γ' : Hom Γ Δ} → γ ~~ γ' → γ' ~~ γ
  trans~~  : ∀ {Γ Δ} {γ γ' γ'' : Hom Γ Δ} → γ ~~ γ' → γ' ~~ γ'' → γ ~~ γ''

refl~ : ∀ {Γ α} {t : Tm Γ α} → t ~ t
refl~ {t = t} = trans~ (sym~ (tmId t)) (tmId t) 

~equivr : ∀ {Γ α} → IsEquivalence (_~_ {Γ} {α})
~equivr = record
  { refl = refl~
  ; sym = sym~
  ; trans = trans~
  }

TmCwf : ∀ {Γ α} → Setoid _ _
TmCwf {Γ} {α} = record
  { Carrier = Tm Γ α
  ; _≈_ = _~_
  ; isEquivalence = ~equivr
  }

refl~~ : ∀ {Γ Δ} {γ : Hom Γ Δ} → γ ~~ γ
refl~~ {γ = γ} = trans~~ (sym~~ (idL γ)) (idL γ)

~~equivr : ∀ {Γ Δ} → IsEquivalence (_~~_ {Γ} {Δ})
~~equivr = record
  { refl = refl~~
  ; sym = sym~~
  ; trans = trans~~
  }

HmSetoid : ∀ {Γ Δ} → Setoid _ _
HmSetoid {Γ} {Δ} = record
  { Carrier = Hom Γ Δ
  ; _≈_ = _~~_
  ; isEquivalence = ~~equivr
  }

homε~<> : ∀ {Γ} (γ : Hom Γ ε) → γ ~~ <>
homε~<> γ = begin
  γ            ≈⟨ sym~~ (idL γ) ⟩
  id {ε} ∘ γ   ≈⟨ cong-∘ id₀ refl~~ ⟩
  <> ∘ γ       ≈⟨ ∘<> γ ⟩
  <>           ∎
  where open EqR (HmSetoid {_} {_})

surj-<,> : ∀ {Γ Δ α} (γ : Hom Γ (Δ , α)) → γ ~~ < p ∘ γ , q [ γ ] >
surj-<,> γ = begin
  γ                     ≈⟨ sym~~ (idL γ) ⟩
  id ∘ γ                ≈⟨ cong-∘ varp refl~~ ⟩
  < p , q > ∘ γ         ≈⟨ maps q p γ ⟩
  < p ∘ γ , q [ γ ] >   ∎
  where open EqR (HmSetoid {_} {_})
