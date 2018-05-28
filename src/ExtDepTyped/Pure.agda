module ExtDepTyped.Pure where

open import Data.Nat renaming (ℕ to Nat) using (_+_ ; suc ; zero)
open import Data.Fin as Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_] ; _∈_)
open import Data.Vec.Properties
open import Data.Vec.All as All using (All)
open import Data.Vec.All.Properties using (gmap)
open import Function hiding (id ; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Unityped.ImpSub renaming (_∙_ to _∘_ ; _/_ to _[_]) -- Contains renamings and relevant operations

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Fin n → Ctx (1 + n)
  
toVec : ∀ {n} → Ctx n → Vec (Fin n) n
toVec ⋄       = []
toVec (Γ ∙ A) = suc A ∷ map suc (toVec Γ) 

lookup' : ∀ {n} → Fin n → Ctx n → Fin n
lookup' i Γ = lookup i (toVec Γ)

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

  -- tyhjä


data _⊢_∈_ where

  tm-var : ∀ {n} {i : Fin n} {Γ : Ctx n}
           → Γ ⊢
           → Γ ⊢ i ∈ (lookup' i Γ)

data _⊢_∈s_ where

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → ⋄ ⊢ [] ∈s Γ

  ⊢<,> : ∀ {m n Δ Γ A i} {γ : Ren m n}
         → Γ ⊢ γ ∈s Δ
         → Γ ⊢ A
         → Δ ⊢ i ∈ (A [ γ ])
         → Γ ∙ A ⊢ (i ∷ γ) ∈s Δ

wf⁻¹ : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢
wf⁻¹ (c-ext Γ⊢ _) = Γ⊢

wf⁻² : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢ A
wf⁻² (c-ext _ ⊢A) = ⊢A

wfR-wf₁ : ∀ {m n Γ Δ} {ρ : Ren m n} → Γ ⊢ ρ ∈s Δ → Δ ⊢
wfR-wf₁ (⊢<> ⊢Δ)      = ⊢Δ
wfR-wf₁ (⊢<,> ⊢ρ _ _) = wfR-wf₁ ⊢ρ

wfR-wf₂ : ∀ {m n Γ Δ} {ρ : Ren m n} → Γ ⊢ ρ ∈s Δ → Γ ⊢
wfR-wf₂ (⊢<> ⊢Γ)       = c-emp
wfR-wf₂ (⊢<,> ⊢ρ ⊢A _) = c-ext (wfR-wf₂ ⊢ρ) ⊢A

getTy : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Fin n
getTy {A = A} _ = A

typeconv : ∀ {n} {Γ : Ctx n} {i A B}
           → Γ ⊢ i ∈ A
           → Γ ⊢ i ∈ B
           → A ≡ B
typeconv (tm-var _) (tm-var _) = refl

map-suc-preserv : ∀ {m n Γ Δ A} (ρ : Ren m n)
                  → Δ ⊢ A
                  → Γ ⊢ ρ ∈s Δ
                  → Γ ⊢ map suc ρ ∈s Δ ∙ A
map-suc-preserv []      ⊢A  (⊢<> Γ⊢)        = ⊢<> (c-ext Γ⊢ ⊢A)
map-suc-preserv (x ∷ ρ) ⊢A' (⊢<,> ⊢ρ ⊢A ⊢x) = ⊢<,> (map-suc-preserv ρ ⊢A' ⊢ρ) ⊢A {!!}

postulate
  subR-ty : ∀ {m n Γ Δ A} {ρ : Ren m n}
            → Γ ⊢ A
            → Γ ⊢ ρ ∈s Δ
            → Δ ⊢ (A [ ρ ])

p-preserves : ∀ {n A} {Γ : Ctx n} → Γ ⊢ A → Γ ⊢ p ∈s Γ ∙ A

suc-pr : ∀ {n A B} {Γ : Ctx n}
         → Γ ⊢ A
         → Γ ⊢ B
         → Γ ∙ A ⊢ suc B
suc-pr {A = A} {B} ⊢A ⊢B
  rewrite sym $ lookup-p B = subR-ty ⊢B (p-preserves ⊢A) 

toAll : ∀ {n} {Γ : Ctx n} → Γ ⊢ → All (Γ ⊢_) (toVec Γ)
toAll c-emp         = All.[]
toAll (c-ext Γ⊢ ⊢A) = suc-pr ⊢A ⊢A All.∷ gmap (suc-pr ⊢A) (toAll Γ⊢)

lookup-wf : ∀ {n} {Γ : Ctx n} (i : Fin n)
            → Γ ⊢
            → Γ ⊢ lookup' i Γ
lookup-wf i Γ⊢ = All.lookup i (toAll Γ⊢)

wfTm-wfTy : ∀ {n} {Γ : Ctx n} {i A} → Γ ⊢ i ∈ A → Γ ⊢ A
wfTm-wfTy (tm-var {i = i} Γ⊢) = lookup-wf i Γ⊢

wfTm-wf : ∀ {n} {Γ : Ctx n} {i A} → Γ ⊢ i ∈ A → Γ ⊢
wfTm-wf (tm-var Γ⊢) = Γ⊢

postulate  
  wfTy-wf : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ⊢

q-preserves : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ∙ A ⊢ zero ∈ (A [ p ])
q-preserves {Γ = Γ} {A} ⊢A = help (tm-var (c-ext (wfTy-wf ⊢A) ⊢A))
 where help : (Γ ∙ A) ⊢ zero ∈ suc A → (Γ ∙ A) ⊢ zero ∈ (A [ p ])
       help hyp rewrite lookup-p A = hyp

-- Does this hold?
↑-preserv : ∀ {m n Γ Δ A B} {ρ : Ren m n}
            → Γ ⊢ A
            → Δ ⊢ B
            → Γ ⊢ ρ ∈s Δ
            → Γ ∙ A ⊢ ↑ ρ ∈s Δ ∙ B
↑-preserv {Γ = Γ} {Δ} {A} {B} {ρ} ⊢A ⊢B ⊢ρ =
  let Δ⊢ = wfR-wf₁ ⊢ρ
      ΔC = c-ext Δ⊢ ⊢B
      ∈sucB = tm-var {i = zero} ΔC
  in ⊢<,> (map-suc-preserv _ ⊢B ⊢ρ) ⊢A {!!}

id-preserves : ∀ {n} {Γ : Ctx n} → Γ ⊢ → Γ ⊢ id ∈s Γ
id-preserves {Γ = ⋄}     Γ⊢            = ⊢<> Γ⊢
id-preserves {Γ = Γ ∙ A} (c-ext Γ⊢ ⊢A) = ↑-preserv ⊢A ⊢A (id-preserves Γ⊢)

p-preserves ⊢A = map-suc-preserv _ ⊢A (id-preserves (wfTy-wf ⊢A))

lookup-preserv : ∀ {n m Γ Δ} i (ρ : Vec (Fin m) n)
                 → Γ ⊢ ρ ∈s Δ
                 → Δ ⊢ lookup i ρ ∈ (lookup' i Γ [ ρ ])
lookup-preserv zero (_ ∷ _) (⊢<,> _ _ ⊢x) = ⊢x
lookup-preserv {Γ = Γ ∙ _} (suc i) (_ ∷ ρ) (⊢<,> ⊢ρ _ _)
  rewrite lookup-map i Fin.suc (toVec Γ) = lookup-preserv i ρ ⊢ρ 

sub-preserves : ∀ {m n Γ Δ A i} {ρ : Ren m n}
                → Γ ⊢ i ∈ A
                → Γ ⊢ ρ ∈s Δ
                → Δ ⊢ i [ ρ ] ∈ (A [ ρ ])
sub-preserves (tm-var {i = i} _) ⊢ρ = lookup-preserv i _ ⊢ρ

comp-preserv : ∀ {m n k Γ Δ Θ} {ρ₁ : Ren n k} {ρ₂ : Ren m n}
               → Θ ⊢ ρ₁ ∈s Δ
               → Δ ⊢ ρ₂ ∈s Γ
               → Θ ⊢ ρ₁ ∘ ρ₂ ∈s Γ
comp-preserv (⊢<> Δ⊢) ⊢ρ₂ = ⊢<> (wfR-wf₁ ⊢ρ₂)
comp-preserv {Γ = Γ} {Θ = _ ∙ A}
             {ρ₁ = x ∷ ρ₁} {ρ₂ = ρ₂}
             (⊢<,> ⊢ρ₁ ⊢A ⊢i) ⊢ρ₂ = ⊢<,> (comp-preserv ⊢ρ₁ ⊢ρ₂) ⊢A (h (sub-preserves ⊢i ⊢ρ₂))
  where h : Γ ⊢ x [ ρ₂ ] ∈ (A [ ρ₁ ] [ ρ₂ ]) → Γ ⊢ x [ ρ₂ ] ∈ (A [ ρ₁ ∘ ρ₂ ])
        h hyp rewrite subComp A ρ₁ ρ₂ = hyp
