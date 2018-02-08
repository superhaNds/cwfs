-----------------------------------------------------------------------------------------------
-- An implementation of dependently typed lambda calculus with Π and universe ala Russel
-- Substitution is formalized in the meta language, we have variables using de Bruijn indices
-- and substitutions are vectors. Starting from raw syntax, we provide external typing
-- relations.
-----------------------------------------------------------------------------------------------
module Ext-Typed.DTyped.Lambda where

open import Function as F using (_$_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_] ; _∈_)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

-----------------------------------------------------------------------------------------------
-- Terms and types under one data type

infix 10 _·_

data Tm (n : Nat) : Set where
  var : (i : Fin n) → Tm n
  ƛ   : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n
  Π   : Tm n → Tm (suc n) → Tm n
  U   : Tm n

q : ∀ {n} → Tm (suc n)
q = var zero

-- Renamings (substitutions for variables)

Ren : Nat → Nat → Set
Ren m n = Vec (Fin m) n

-- Substitutions

Sub : Nat → Nat → Set
Sub m n = Vec (Tm m) n

-- identity substitution

id : ∀ {n} → Sub n n
id = tabulate var

infix 7 _,_

_,_ : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)
ρ , t = t ∷ ρ

p : ∀ {n} → Sub (suc n) n
p = tabulate (var F.∘ suc)

-- lifting and extending a renaming

↑-ren : ∀ {m n} → Ren m n → Ren (suc m) (suc n)
↑-ren ρ = zero ∷ map suc ρ

-- renaming operation

ren : ∀ {m n} → Tm n → Ren m n → Tm m
ren (var i) ρ = var (lookup i ρ)
ren (ƛ t)   ρ = ƛ (ren t (↑-ren ρ))
ren (t · u) ρ = (ren t ρ) · (ren u ρ)
ren (Π A B) ρ = Π (ren A ρ) (ren B (↑-ren ρ))
ren U       _ = U

-- weakening a term

wk : ∀ {n} → Tm n → Tm (suc n)
wk t = ren t (tabulate suc)

-- weakening a substitution

wk-sub : ∀ {m n} → Sub m n → Sub (suc m) n
wk-sub = map wk

-- Lifting and extending a substitution

↑_ : ∀ {m n} (ρ : Sub m n) → Sub (suc m) (suc n)
↑ ρ = wk-sub ρ , q

id' : ∀ {n} → Sub n n
id' {zero} = []
id' {suc n} = ↑ id'

wk⋆ : ∀ k {n} → Sub (k + n) n
wk⋆ zero    = id'
wk⋆ (suc k) = map wk (wk⋆ k)

p' : ∀ {n} → Sub (suc n) n
p' = wk⋆ 1

-- Substitution as a meta operation

_[_] : ∀ {m n} (t : Tm n) (ρ : Sub m n) → Tm m
var i   [ ρ ] = lookup i ρ
ƛ t     [ ρ ] = ƛ (t [ ↑ ρ ])
(t · u) [ ρ ] = (t [ ρ ]) · (u [ ρ ])
Π A B   [ ρ ] = Π (A [ ρ ]) (B [ ↑ ρ ])
U       [ _ ] = U

infix 8 _∘_

-- Compositions of substitutions

_∘_ : ∀ {m n k} → Sub n k → Sub m n → Sub m k
ρ ∘ σ = map (_[ σ ]) ρ

cong-ƛ : ∀ {n} {t t' : Tm (suc n)} → t ≡ t' → ƛ t ≡ ƛ t'
cong-ƛ refl = refl

cong-Π₁ : ∀ {n} {A A' : Tm n} {B} → A ≡ A' → Π A B ≡ Π A' B 
cong-Π₁ refl = refl

cong-Π₂ : ∀ {n} {A : Tm n} {B B'} → B ≡ B' → Π A B ≡ Π A B'
cong-Π₂ refl = refl

cong-sub : ∀ {n m} {t t' : Tm n} {ρ ρ' : Sub m n} →
           t ≡ t' →
           ρ ≡ ρ' →
           t [ ρ ] ≡ t' [ ρ' ]
cong-sub refl refl = refl

idExt : ∀ {n} → id {suc n} ≡ p , q
idExt {n} = refl

lookup-id : ∀ {n} i → lookup i (id {n}) ≡ var i
lookup-id i = lookup∘tabulate var i

-- These are proven in the unityped work since they share the core definitions

postulate

  lift-idExt : ∀ {n} → ↑ id {n} ≡ (p , q)

  ↑-dist : ∀ {m n k} (ρ : Sub m n) (σ : Sub k m) → ↑ (ρ ∘ σ) ≡ ↑ ρ ∘ ↑ σ

  wk-sub-p : ∀ {n} {t : Tm n} → wk t ≡ t [ p ]
  
wkSub-∘-p : ∀ {m n} (ρ : Sub m n) → wk-sub ρ ≡ ρ ∘ p
wkSub-∘-p [] = refl
wkSub-∘-p (t ∷ ρ) = begin
  wk-sub (t ∷ ρ)       ≡⟨⟩
  wk t ∷ wk-sub ρ      ≡⟨ cong (_∷ wk-sub ρ) wk-sub-p ⟩
  t [ p ] ∷ wk-sub ρ   ≡⟨ cong (t [ p ] ∷_) (wkSub-∘-p ρ) ⟩
  t [ p ] ∷ ρ ∘ p      ∎

↑-wkSub : ∀ {m n} {γ : Sub m n} → ↑ γ ≡ (γ ∘ p , q)
↑-wkSub {γ = γ} = cong (_, q) (wkSub-∘-p γ)

subId : ∀ {n} (t : Tm n) → t [ id ] ≡ t
subId (var i) = lookup-id i
subId (ƛ t)   = cong-ƛ (trans (cong (t [_]) lift-idExt) (subId t))
subId (t · u) = cong₂ _·_ (subId t) (subId u)
subId (Π A B) = cong₂ Π (subId A) (trans (cong (B [_]) lift-idExt) (subId B))
subId U       = refl

subComp : ∀ {m n k} t (ρ : Sub m n) (σ : Sub k m) → t [ ρ ∘ σ ] ≡ t [ ρ ] [ σ ]
subComp U _ _ = refl          
subComp (var zero)    (x ∷ ρ) σ = refl
subComp (var (suc i)) (x ∷ ρ) σ = subComp (var i) ρ σ
subComp (ƛ t)   ρ σ = cong-ƛ (trans (cong (t [_]) (↑-dist ρ σ)) (subComp t (↑ ρ) (↑ σ)))
subComp (t · u) ρ σ = cong₂ _·_ (subComp t ρ σ) (subComp u ρ σ)
subComp (Π A B) ρ σ = begin
  Π (A [ ρ ∘ σ ])   (B [ ↑ (ρ ∘ σ) ])   ≡⟨ cong-Π₁ (subComp A ρ σ) ⟩
  Π (A [ ρ ] [ σ ]) (B [ ↑ (ρ ∘ σ) ])   ≡⟨ cong-Π₂ (cong (B [_]) (↑-dist ρ σ)) ⟩
  Π (A [ ρ ] [ σ ]) (B [ ↑ ρ ∘ ↑ σ ])   ≡⟨ cong-Π₂ (subComp B (↑ ρ) (↑ σ)) ⟩
  Π (A [ ρ ] [ σ ]) (B [ ↑ ρ ] [ ↑ σ ]) ∎
        
