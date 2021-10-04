-------------------------------------------------------------------------------
-- A Ucwf with implicit substitutions. Essentially a theory of n-place
-- functions with substitution formalized as a meta-level operation.
-------------------------------------------------------------------------------
module Unityped.ImpSub where

open import Data.Nat renaming (ℕ to Nat) using (_+_ ; suc ; zero)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_] ; lookup)
open import Data.Vec.Properties hiding (lookup-map ; map-lookup-allFin ; tabulate∘lookup)
open import Function hiding (id)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unityped.Ucwf
open ≡-Reasoning

-------------------------------------------------------------------------------
-- Substitutions are vectors that contains Fin elements
-- They are referred to as renamings (Ren)

-- Renamings

Ren : Nat → Nat → Set
Ren m = Vec (Fin m)

-- Lifts and extends a renaming

↑ : ∀ {m n} → Ren m n → Ren (1 + m) (1 + n)
↑ ρ = zero ∷ map suc ρ

-- generalized ↑

_↑⋆_ : ∀ {m n} (k : Nat) → Ren m n → Ren (k + m) (k + n)
zero  ↑⋆ ρ = ρ
suc k ↑⋆ ρ = ↑ (k ↑⋆ ρ)

-- identity renaming

id : ∀ {n} → Ren n n
id {zero}  = []
id {suc n} = ↑ id

-- generalized projection renaming (AKA weakening)

p⋆ : ∀ k {n} → Ren (k + n) n
p⋆ zero    = id
p⋆ (suc k) = map suc (p⋆ k)

-- projection renaming

p : ∀ {n} → Ren (1 + n) n
p = p⋆ 1

infix 12 _∙_


lookup : ∀ {a} {A : Set a} {n} → Fin n → Vec A n → A
lookup zero    (x ∷ _)  = x
lookup (suc i) (x ∷ xs) = lookup i xs

-- renaming composition

_∙_ : ∀ {m n k} → Ren m n → Ren k m → Ren k n
ρ₁ ∙ ρ₂ = map (flip lookup ρ₂) ρ₁

infixl 5 _/_

-- renaming substitution

_/_ : ∀ {m n} → Fin n → Ren m n → Fin m
i / ρ = lookup i ρ

-- composition definition

compExt : ∀ {m n k} (σ : Ren n m) (ρ : Ren k n) t
          → (t ∷ σ) ∙ ρ ≡ ((t / ρ) ∷ σ ∙ ρ )
compExt _ _ _ = refl

lookup-map : ∀ {a b n} {A : Set a} {B : Set b}
             i (f : A → B) (xs : Vec A n) → lookup i (map f xs) ≡ f (lookup i xs)
lookup-map zero    _ (_ ∷ _)  = refl
lookup-map (suc i) f (x ∷ xs) = lookup-map i f xs

-- lookup in id returns the input Fin

lookup-id : ∀ {n} (i : Fin n) → lookup i id ≡ i
lookup-id zero    = refl
lookup-id (suc i) = trans (lookup-map i suc id) (cong suc (lookup-id i))

-- lookup in p returns the successor of the input Fin

lookup-p : ∀ {n} (i : Fin n) → lookup i p ≡ suc i
lookup-p i = trans (lookup-map i suc id) (cong suc (lookup-id i))

-- An extended id is the projection with zero

idExt : ∀ {n} → id {1 + n} ≡ (zero ∷ p)
idExt {zero}  = refl
idExt {suc n} = cong ↑ idExt

-- Empty vector is a left zero in composition

left-zero : ∀ {n m} {ρ : Ren m n} → [] ∙ ρ ≡ []
left-zero = refl

-- id vanishes when substituted

subId : ∀ {n} {i : Fin n} → i / id ≡ i
subId {i = i} = lookup-id i

-- substitution is associative

subComp : ∀ {m n k} i (ρ : Ren m n) (σ : Ren k m) → i / (ρ ∙ σ) ≡ i / ρ / σ
subComp zero    (_ ∷ _) _ = refl
subComp (suc i) (_ ∷ ρ) σ = subComp i ρ σ

tab-suc : ∀ {n} → Ren (suc n) n
tab-suc = tabulate suc

map-suc-tab : ∀ {n} → map suc (id {n}) ≡ tab-suc {n}
map-suc-tab {zero } = refl
map-suc-tab {suc n} = trans (cong (λ x → suc zero ∷ map suc x) map-suc-tab)
                            (cong (suc zero ∷_) (sym $ tabulate-∘ suc suc))

-- id is the standard's library allFin equivalent

id-allFin : ∀ {n} → id ≡ allFin n
id-allFin {zero}  = refl
id-allFin {suc _} = cong (zero ∷_) map-suc-tab


tabulate∘lookup : ∀ {a n} {A : Set a} (xs : Vec A n) → tabulate (flip lookup xs) ≡ xs
tabulate∘lookup []       = refl
tabulate∘lookup (x ∷ xs) = cong (x ∷_) (tabulate∘lookup xs)

map-lookup-allFin : ∀ {a} {A : Set a} {n} (xs : Vec A n) → map (flip lookup xs) (allFin n) ≡ xs
map-lookup-allFin {n = n} xs = trans (sym $ tabulate-∘ (flip lookup xs) (λ x → x)) (tabulate∘lookup xs)
  --map (λ x → lookup x xs) (allFin n) ≡⟨ P.sym $ tabulate-∘ (λ x → lookup x xs) id ⟩
  --tabulate (λ x → lookup x xs)       ≡⟨ tabulate∘lookup xs ⟩
  --xs                                 ∎
  --where open P.≡-Reasoning

-- mapping looking in p drops the head of the renaming

map-lookup-p : ∀ {m n} (ρ : Ren m (1 + n)) → map (flip lookup ρ) p ≡ tail ρ
map-lookup-p (x ∷ ρ) = begin
  map (flip lookup (x ∷ ρ)) p      ≡⟨ sym (map-∘ (flip lookup (x ∷ ρ)) suc id) ⟩
  map (flip lookup ρ) id           ≡⟨ cong (map (flip lookup ρ)) id-allFin ⟩
  map (flip lookup ρ) (allFin _)   ≡⟨ map-lookup-allFin ρ ⟩
  ρ
  ∎

-- p left in composition drops the head of the renaming

p-∙ : ∀ {m n} {ρ : Ren m n} {i} → p ∙ (i ∷ ρ) ≡ ρ
p-∙ {ρ = ρ} {i} = map-lookup-p (i ∷ ρ)

-- composition is associative

∙-asso : ∀ {m n k j} (ρ₁ : Ren n k) (ρ₂ : Ren m n) (ρ₃ : Ren j m)
         → (ρ₁ ∙ ρ₂) ∙ ρ₃ ≡ ρ₁ ∙ (ρ₂ ∙ ρ₃)
∙-asso [] ρ₂ ρ₃ = refl
∙-asso (i ∷ ρ₁) ρ₂ ρ₃ = begin
  ((i ∷ ρ₁) ∙ ρ₂) ∙ ρ₃            ≡⟨⟩
  (i / ρ₂ / ρ₃) ∷ (ρ₁ ∙ ρ₂) ∙ ρ₃  ≡⟨ cong (_∷ (ρ₁ ∙ ρ₂) ∙ ρ₃ ) (sym $ subComp i ρ₂ ρ₃) ⟩
  (i / ρ₂ ∙ ρ₃) ∷ (ρ₁ ∙ ρ₂) ∙ ρ₃  ≡⟨ cong ((i / ρ₂ ∙ ρ₃) ∷_) (∙-asso ρ₁ ρ₂ ρ₃) ⟩
  (i / ρ₂ ∙ ρ₃) ∷ ρ₁ ∙ (ρ₂ ∙ ρ₃)
  ∎

-- composing p with lifted renaming is weakening 

p-∙-↑ : ∀ {m n} {ρ : Ren m n} → p ∙ (↑ ρ) ≡ map suc ρ
p-∙-↑ {ρ = ρ} = begin
  map (λ i → lookup i (↑ ρ)) p                ≡⟨ sym $ map-∘ _ suc id ⟩
  map (λ i → lookup i (map suc ρ)) id         ≡⟨ cong (map (λ i → lookup i (map suc ρ))) id-allFin ⟩
  map (λ i → lookup i (map suc ρ)) (allFin _) ≡⟨ map-lookup-allFin (map suc ρ) ⟩
  map suc ρ
  ∎

map-suc-p : ∀ {m n} {ρ : Ren m n} → ρ ∙ p ≡ map suc ρ
map-suc-p {ρ = []}    = refl
map-suc-p {ρ = x ∷ ρ} =
  trans (cong (_∷ map (flip lookup p) ρ) (lookup-p x))
        (cong (suc x ∷_) map-suc-p)

-- composing with p is weakening

∙-p : ∀ {m n} {ρ : Ren m n} → ρ ∙ p ≡ p ∙ (↑ ρ)
∙-p = trans (map-cong lookup-p _) (sym p-∙-↑)

-- id is a left identity in composition

idL : ∀ {m n} {ρ : Ren m n} → id ∙ ρ ≡ ρ
idL {ρ = []} = refl
idL {ρ = i ∷ ρ} rewrite p-∙ {ρ = ρ} {i} = refl

-- id is a right identity in composition

idR : ∀ {m n} {ρ : Ren m n} → ρ ∙ id ≡ ρ
idR {ρ = []} = refl
idR {ρ = i ∷ ρ} rewrite subId {i = i}
                      | idR {ρ = ρ} = refl

suc-mapsuc : ∀ {m n} (ρ : Ren m n) i → i / (map suc ρ) ≡ suc (i / ρ)
suc-mapsuc []      ()
suc-mapsuc (_ ∷ _) zero    = refl
suc-mapsuc (_ ∷ ρ) (suc i) = suc-mapsuc ρ i

-- congruence rules

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

-- ↑ distributes over composition

↑-dist : ∀ {m n k} (ρ₁ : Ren m n) (ρ₂ : Ren k m) → ↑ (ρ₁ ∙ ρ₂) ≡ ↑ ρ₁ ∙ ↑ ρ₂
↑-dist ρ₁ ρ₂ = begin
  ↑ (ρ₁ ∙ ρ₂)                                     ≡⟨⟩
  zero ∷ map suc (map (flip lookup ρ₂) ρ₁)        ≡⟨ cong (zero ∷_) (sym $ map-∘ suc (flip lookup ρ₂) ρ₁) ⟩
  zero ∷ map (λ i → suc (lookup i ρ₂)) ρ₁         ≡⟨ cong (zero ∷_) (map-cong (suc-lookup-↑ ρ₂) ρ₁) ⟩
  zero ∷ map (λ i → lookup (suc i) (↑ ρ₂)) ρ₁     ≡⟨ cong (zero ∷_) (map-∘ (flip lookup (↑ ρ₂)) suc ρ₁) ⟩
  zero ∷ map (λ i → lookup i (↑ ρ₂)) (map suc ρ₁) ≡⟨⟩
  ↑ ρ₁ ∙ ↑ ρ₂
  ∎

-- Renamings form a ucwf with propositional equality

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


