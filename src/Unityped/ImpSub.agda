module ImpSub where

open import Data.Nat renaming (ℕ to Nat) using (_+_ ; suc ; zero)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Function hiding (id)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Ucwf
open ≡-Reasoning

Ren : Nat → Nat → Set
Ren m n = Vec (Fin m) n

↑ : ∀ {m n} → Ren m n → Ren (1 + m) (1 + n)
↑ ρ = zero ∷ map suc ρ

_↑⋆_ : ∀ {m n} (k : Nat) → Ren m n → Ren (k + m) (k + n)
zero ↑⋆ ρ = ρ
suc k ↑⋆ ρ = ↑ (k ↑⋆ ρ)

id : ∀ {n} → Ren n n
id {zero}  = []
id {suc n} = ↑ id

p⋆ : ∀ k {n} → Ren (k + n) n
p⋆ zero    = id
p⋆ (suc k) = map suc (p⋆ k)

p : ∀ {n} → Ren (1 + n) n
p = p⋆ 1

infix 12 _∙_

_∙_ : ∀ {m n k} → Ren m n → Ren k m → Ren k n
ρ₁ ∙ ρ₂ = map (flip lookup ρ₂) ρ₁

infixl 5 _/_

_/_ : ∀ {m n} → Fin n → Ren m n → Fin m
i / ρ = lookup i ρ

compExt : ∀ {m n k} (σ : Ren n m) (ρ : Ren k n) t
          → (t ∷ σ) ∙ ρ ≡ ((t / ρ) ∷ σ ∙ ρ )
compExt _ _ _ = refl

lookup-map : ∀ {a b n} {A : Set a} {B : Set b}
             i (f : A → B) (xs : Vec A n) → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map zero    _ (_ ∷ _)  = refl
lookup-map (suc i) f (x ∷ xs) = lookup-map i f xs

lookup-id : ∀ {n} (i : Fin n) → lookup i id ≡ i
lookup-id zero    = refl
lookup-id (suc i) = trans (lookup-map i suc id) (cong suc (lookup-id i))

lookup-p : ∀ {n} (i : Fin n) → lookup i p ≡ suc i
lookup-p i = trans (lookup-map i suc id) (cong suc (lookup-id i))

idExt : ∀ {n} → id {1 + n} ≡ (zero ∷ p)
idExt {zero}  = refl
idExt {suc n} = cong ↑ idExt

left-zero : ∀ {n m} {ρ : Ren m n} → [] ∙ ρ ≡ []
left-zero = refl

subId : ∀ {n} {i : Fin n} → i / id ≡ i
subId {i = i} = lookup-id i

subComp : ∀ {m n k} i (ρ : Ren m n) (σ : Ren k m) → i / (ρ ∙ σ) ≡ i / ρ / σ
subComp zero    (_ ∷ _) _ = refl
subComp (suc i) (_ ∷ ρ) σ = subComp i ρ σ

tab-suc : ∀ {n} → Ren (suc n) n
tab-suc = tabulate suc

map-suc-tab : ∀ {n} → map suc (id {n}) ≡ tab-suc {n}
map-suc-tab {zero } = refl
map-suc-tab {suc n} = trans (cong (λ x → suc zero ∷ map suc x) map-suc-tab)
                            (cong (suc zero ∷_) (sym $ tabulate-∘ suc suc))

id-allFin : ∀ {n} → id ≡ allFin n
id-allFin {zero}  = refl
id-allFin {suc _} = cong (zero ∷_) map-suc-tab

map-lookup-p : ∀ {m n} (ρ : Ren m (1 + n)) → map (flip lookup ρ) p ≡ tail ρ
map-lookup-p (x ∷ ρ) = begin
  map (flip lookup (x ∷ ρ)) p      ≡⟨ sym (map-∘ (flip lookup (x ∷ ρ)) suc id) ⟩
  map (flip lookup ρ) id           ≡⟨ cong (map (flip lookup ρ)) id-allFin ⟩
  map (flip lookup ρ) (allFin _)   ≡⟨ map-lookup-allFin ρ ⟩
  ρ
  ∎

p-∙ : ∀ {m n} {ρ : Ren m n} {i} → p ∙ (i ∷ ρ) ≡ ρ
p-∙ {ρ = ρ} {i} = map-lookup-p (i ∷ ρ)

∙-asso : ∀ {m n k j} (ρ₁ : Ren n k) (ρ₂ : Ren m n) (ρ₃ : Ren j m)
         → (ρ₁ ∙ ρ₂) ∙ ρ₃ ≡ ρ₁ ∙ (ρ₂ ∙ ρ₃)
∙-asso [] ρ₂ ρ₃ = refl
∙-asso (i ∷ ρ₁) ρ₂ ρ₃ = begin
  ((i ∷ ρ₁) ∙ ρ₂) ∙ ρ₃            ≡⟨⟩
  (i / ρ₂ / ρ₃) ∷ (ρ₁ ∙ ρ₂) ∙ ρ₃  ≡⟨ cong (_∷ (ρ₁ ∙ ρ₂) ∙ ρ₃ ) (sym $ subComp i ρ₂ ρ₃) ⟩
  (i / ρ₂ ∙ ρ₃) ∷ (ρ₁ ∙ ρ₂) ∙ ρ₃  ≡⟨ cong ((i / ρ₂ ∙ ρ₃) ∷_) (∙-asso ρ₁ ρ₂ ρ₃) ⟩
  (i / ρ₂ ∙ ρ₃) ∷ ρ₁ ∙ (ρ₂ ∙ ρ₃)
  ∎

p-∙-↑ : ∀ {m n} {ρ : Ren m n} → p ∙ (↑ ρ) ≡ map suc ρ
p-∙-↑ {ρ = ρ} = begin
  map (λ i → lookup i (↑ ρ)) p                ≡⟨ sym $ map-∘ _ suc id ⟩
  map (λ i → lookup i (map suc ρ)) id         ≡⟨ cong (map (λ i → lookup i (map suc ρ))) id-allFin ⟩
  map (λ i → lookup i (map suc ρ)) (allFin _) ≡⟨ map-lookup-allFin _ ⟩
  map suc ρ
  ∎

∙-p : ∀ {m n} {ρ : Ren m n} → ρ ∙ p ≡ p ∙ (↑ ρ)
∙-p = trans (map-cong lookup-p _) (sym p-∙-↑)

idL : ∀ {m n} {ρ : Ren m n} → id ∙ ρ ≡ ρ
idL {ρ = []} = refl
idL {ρ = i ∷ ρ} rewrite p-∙ {ρ = ρ} {i} = refl

idR : ∀ {m n} {ρ : Ren m n} → ρ ∙ id ≡ ρ
idR {ρ = []} = refl
idR {ρ = i ∷ ρ} rewrite subId {i = i}
                      | idR {ρ = ρ} = refl

cong-, : ∀ {m n} {σ₁ σ₂ : Ren m n} {t₁ t₂}
           → t₁ ≡ t₂
           → σ₁ ≡ σ₂
           → (t₁ ∷ σ₁) ≡ (t₂ ∷ σ₂)
cong-, refl refl = refl

cong-sub : ∀ {m n} {σ₁ σ₂ : Ren m n} {t₁ t₂}
           → t₁ ≡ t₂
           → σ₁ ≡ σ₂
           → t₁ / σ₁ ≡ t₂ / σ₂ 
cong-sub refl refl = refl

cong-∙ : ∀ {m n k} {σ₁ σ₂ : Ren n k} {ρ₁ ρ₂ : Ren m n}
         → σ₁ ≡ σ₂
         → ρ₁ ≡ ρ₂
         → σ₁ ∙ ρ₁ ≡ σ₂ ∙ ρ₂
cong-∙ refl refl = refl

suc-lookup-↑ : ∀ {m n} (ρ : Ren m n) (i : Fin n) → suc (lookup i ρ) ≡ lookup (suc i) (↑ ρ)
suc-lookup-↑ (_ ∷ _) zero    = refl
suc-lookup-↑ (j ∷ ρ) (suc i) = sym (lookup-map i suc ρ)

↑-dist : ∀ {m n k} (ρ₁ : Ren m n) (ρ₂ : Ren k m) → ↑ (ρ₁ ∙ ρ₂) ≡ ↑ ρ₁ ∙ ↑ ρ₂
↑-dist ρ₁ ρ₂ = begin
  ↑ (ρ₁ ∙ ρ₂)                                     ≡⟨⟩
  zero ∷ map suc (map (flip lookup ρ₂) ρ₁)        ≡⟨ cong (zero ∷_) (sym $ map-∘ suc (flip lookup ρ₂) ρ₁) ⟩
  zero ∷ map (λ i → suc (lookup i ρ₂)) ρ₁         ≡⟨ cong (zero ∷_) (map-cong (suc-lookup-↑ ρ₂) ρ₁) ⟩
  zero ∷ map (λ i → lookup (suc i) (↑ ρ₂)) ρ₁     ≡⟨ cong (zero ∷_) (map-∘ (flip lookup (↑ ρ₂)) suc ρ₁) ⟩
  zero ∷ map (λ i → lookup i (↑ ρ₂)) (map suc ρ₁) ≡⟨⟩
  ↑ ρ₁ ∙ ↑ ρ₂
  ∎

ImpSubUcwf : Ucwf
ImpSubUcwf = record
               { Tm        = Fin
               ; Sub       = Ren
               ; _~_       = _≡_
               ; _≈_       = _≡_
               ; IsEquivT  = isEquivalence
               ; IsEquivS  = isEquivalence
               ; id        = id
               ; _∘_       = _∙_
               ; _[_]      = _/_
               ; <>        = []
               ; <_,_>     = flip _∷_
               ; p         = p
               ; q         = zero
               ; id-zero   = refl
               ; left-zero = refl
               ; idExt     = refl
               ; idL       = idL
               ; idR       = idR
               ; assoc     = λ {m} {n} {κ} {ι} {σ₁} {σ₂} {σ₃} → ∙-asso σ₁ σ₂ σ₃
               ; subId     = subId
               ; pCons     = p-∙
               ; qCons     = refl
               ; subComp   = λ {_} {_} {_} {t} {σ} {ρ} → subComp t σ ρ
               ; compExt   = refl
               ; cong-<,>  = cong-,
               ; cong-sub  = cong-sub
               ; cong-∘    = cong-∙
               }
