module Unityped.ImpSub.LamUcwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function as F using (_$_ ; flip ; const)
open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Unityped.ImpSub.Beta
open import Unityped.ImpSub.UcwfImpSub
open import Unityped.ImpSub.Properties
open import Unityped.ImpSub.Syntax
open import Unityped.ImpSub.Substitution

idExt~ : ∀ {n} → id {1 + n} ≈βη (p , q)
idExt~ = ≡-to-≈βη idExt

subId~ : ∀ {n} (t : Tm n) → t [ id ] ~βη t
subId~ t = ≡-to~βη (subId t)

subComp~ : ∀ {m n k} (t : Tm n) (ρ : Subst m n) (σ : Subst k m)
           → t [ ρ ∘ σ ] ~βη t [ ρ ] [ σ ]
subComp~ t ρ σ = ≡-to~βη (subComp t ρ σ)

id₀~ : id {0} ≈βη []
id₀~ = refl≈βη

[]-lzero~ : ∀ {m n} (ρ : Subst m n) → [] ∘ ρ ≈βη []
[]-lzero~ _ = refl≈βη

pCons~ : ∀ {n k} (σ : Subst n k) t → p ∘ (σ , t) ≈βη σ
pCons~ σ t = ≡-to-≈βη (pCons σ t)

assoc~ : ∀ {m n k j} (σ : Subst m n) (γ : Subst k m) (δ : Subst j k)
         → (σ ∘ γ) ∘ δ ≈βη σ ∘ (γ ∘ δ)
assoc~ σ γ δ = ≡-to-≈βη (assoc σ γ δ)

idL~ : ∀ {m n} (σ : Subst m n) → id ∘ σ ≈βη σ
idL~ σ = ≡-to-≈βη (idL σ)

idR~ : ∀ {m n} (σ : Subst m n) → σ ∘ id ≈βη σ
idR~ σ = ≡-to-≈βη (idR σ)

qCons~ : ∀ {m n} (σ : Subst m n) t → q [ σ , t ] ~βη t
qCons~ σ  t = refl~βη

compExt~ : ∀ {m n} (σ : Subst n m) (γ : Subst m n) t
           → (σ , t) ∘ γ ≈βη (σ ∘ γ) , t [ γ ]
compExt~ σ γ t = refl≈βη

