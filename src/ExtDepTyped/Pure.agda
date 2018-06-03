module ExtDepTyped.Pure where

open import Data.Nat renaming (ℕ to Nat) using (_+_ ; suc ; zero)
open import Data.Fin as Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_] ; _∈_)
open import Data.Vec.Properties
open import Data.Vec.All as All using (All)
open import Data.Vec.All.Properties using (gmap)
open import Function hiding (id ; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Unityped.ImpSub renaming (_∙_ to _∘_)

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Fin n → Ctx (1 + n)

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _⊢_∈s_

data _⊢ : ∀ {n} (Γ : Ctx n) → Set

data _⊢_ : ∀ {n} (Γ : Ctx n) (A : Fin n) → Set

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Fin n) (A : Fin n) → Set

data _⊢_∈s_ : ∀ {m n} → Ctx n → Ren m n → Ctx m → Set

data _⊢ where

  c-emp : ⋄ ⊢

  c-ext : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢
          → Γ ⊢ A
          → Γ ∙ A ⊢
          
data _⊢_ where

data _⊢_∈_ where

  ty-zero : ∀ {n} {Γ : Ctx n} {A : Fin n}
            → (Γ ∙ A) ⊢ zero ∈ suc A
              
  ty-suc : ∀ {n} {Δ : Ctx n} {A B i}
           → Δ ⊢ i ∈ A
           → (Δ ∙ B) ⊢ suc i ∈ suc A

data _⊢_∈s_ where

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → ⋄ ⊢ [] ∈s Γ

  ⊢<,> : ∀ {m n Δ Γ A i} {ρ : Ren m n}
         → Γ ⊢ ρ ∈s Δ
         → Γ ⊢ A
         → Δ ⊢ i ∈ (A / ρ)
         → Γ ∙ A ⊢ (i ∷ ρ) ∈s Δ

wf⁻¹ : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢
wf⁻¹ (c-ext Γ⊢ _) = Γ⊢

wf⁻² : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢ A
wf⁻² (c-ext _ ⊢A) = ⊢A

sucs-lemma : ∀ {m n Δ A i} (ρ : Ren m n)
             → Δ ⊢ suc i ∈ suc (A / ρ)
             → Δ ⊢ suc i ∈ (A / (map suc ρ))
sucs-lemma {A = A} ρ ⊢i rewrite suc-mapsuc ρ A = ⊢i                  

ty-of : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Fin n
ty-of {A = A} _ = A

map-suc-preserv : ∀ {m n Γ Δ A} (ρ : Ren m n)
                  → Δ ⊢ A
                  → Γ ⊢ ρ ∈s Δ
                  → Γ ⊢ map suc ρ ∈s Δ ∙ A
map-suc-preserv         []      ⊢A (⊢<> x)         = ⊢<> (c-ext x ⊢A)
map-suc-preserv {A = C} (_ ∷ ρ) ⊢C (⊢<,> ⊢ρ ⊢A ⊢x) = ⊢<,> (map-suc-preserv ρ ⊢C ⊢ρ) ⊢A (sucs-lemma {A = ty-of ⊢A} ρ (ty-suc ⊢x))

ty-q : ∀ {n} {Γ : Ctx n} {A} → (Γ ∙ A) ⊢ zero ∈ (A / p)
ty-q {A = A} rewrite lookup-p A = ty-zero

⊢id : ∀ {n} {Γ : Ctx n}
      → Γ ⊢
      → Γ ⊢ id ∈s Γ
⊢id {Γ = ⋄}      c-emp        = ⊢<> c-emp
⊢id {Γ = Γ ∙ A} (c-ext Γ⊢ ⊢A) = ⊢<,> (map-suc-preserv id ⊢A (⊢id Γ⊢)) ⊢A ty-q

postulate 
  wfTy-wf : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ⊢

⊢p : ∀ {n} {Γ : Ctx n} {A}
     → Γ ⊢ A
     → Γ ⊢ p ∈s (Γ ∙ A)
⊢p ⊢A = map-suc-preserv id ⊢A (⊢id (wfTy-wf ⊢A))

sub-preserves : ∀ {m n Γ Δ A i} {ρ : Ren m n}
                → Γ ⊢ i ∈ A
                → Γ ⊢ ρ ∈s Δ
                → Δ ⊢ i / ρ ∈ (A / ρ)
sub-preserves ty-zero     (⊢<,> _ _ ⊢i) = ⊢i
sub-preserves (ty-suc ⊢i) (⊢<,> ⊢ρ _ _) = sub-preserves ⊢i ⊢ρ

wfR-wf₁ : ∀ {m n Γ Δ} {ρ : Ren m n} → Γ ⊢ ρ ∈s Δ → Δ ⊢
wfR-wf₁ (⊢<> ⊢Δ)      = ⊢Δ
wfR-wf₁ (⊢<,> ⊢ρ _ _) = wfR-wf₁ ⊢ρ

wfR-wf₂ : ∀ {m n Γ Δ} {ρ : Ren m n} → Γ ⊢ ρ ∈s Δ → Γ ⊢
wfR-wf₂ (⊢<> ⊢Γ)       = c-emp
wfR-wf₂ (⊢<,> ⊢ρ ⊢A _) = c-ext (wfR-wf₂ ⊢ρ) ⊢A

comp-lemma : ∀ {n m k x Γ A} {ρ₁ : Ren k n} {ρ₂ : Ren m k}
             → Γ ⊢ x / ρ₂ ∈ (A / ρ₁ / ρ₂ )
             → Γ ⊢ x / ρ₂ ∈ (A / (ρ₁ ∘ ρ₂))
comp-lemma {A = A} {ρ₁} {ρ₂} hyp rewrite subComp A ρ₁ ρ₂ = hyp

comp-preserv : ∀ {m n k Γ Δ Θ} {ρ₁ : Ren n k} {ρ₂ : Ren m n}
               → Θ ⊢ ρ₁ ∈s Δ
               → Δ ⊢ ρ₂ ∈s Γ
               → Θ ⊢ ρ₁ ∘ ρ₂ ∈s Γ
comp-preserv (⊢<> _) ⊢ρ₂ = ⊢<> (wfR-wf₁ ⊢ρ₂)
comp-preserv {Γ = Γ} {Θ = _ ∙ A}
             {ρ₁ = x ∷ ρ₁} {ρ₂ = ρ₂}
             (⊢<,> ⊢ρ₁ ⊢A ⊢i) ⊢ρ₂ = ⊢<,> (comp-preserv ⊢ρ₁ ⊢ρ₂) ⊢A (comp-lemma {x = x} {A = A} (sub-preserves ⊢i ⊢ρ₂))
