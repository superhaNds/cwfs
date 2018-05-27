module ExtDepTyped.ImpSubTy where

open import Function as F using (_$_ ; flip)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_] ; _∈_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import ExtDepTyped.Raw.ImpSub

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

toVec : ∀ {n} → Ctx n → Vec (Tm n) n
toVec ⋄       = []
toVec (Γ ∙ A) = map weaken (toVec Γ) , weaken A

lookup' : ∀ {n} → Fin n → Ctx n → Tm n
lookup' i Γ = lookup i (toVec Γ)

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _⊢_∈s_

data _⊢ : ∀ {n} (Γ : Ctx n) → Set

data _⊢_ : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Tm n) (A : Tm n) → Set

data _⊢_∈s_ : ∀ {m n} → Ctx n → Sub m n → Ctx m → Set

data _⊢ where

  c-emp : ⋄ ⊢

  c-ext : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢
          → Γ ⊢ A
          → Γ ∙ A ⊢
          
data _⊢_ where

  ty-U : ∀ {n} {Γ : Ctx n}
         → Γ ⊢
         → Γ ⊢ U         

  ty-∈U : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A ∈ U
          → Γ ⊢ A

  ty-Π-F : ∀ {n} {Γ : Ctx n} {A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ Π A B

data _⊢_∈_ where

  tm-var : ∀ {n} {i : Fin n} {Γ : Ctx n}
           → Γ ⊢
           → Γ ⊢ var i ∈ lookup' i Γ

  tm-app : ∀ {n} {Γ : Ctx n} {f t A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ f ∈ Π A B
           → Γ ⊢ t ∈ A
           → Γ ⊢ app f t ∈ B [ id , t ]
           
  tm-Π-I : ∀ {n} {Γ : Ctx n} {A B t}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ∙ A ⊢ t ∈ B
           → Γ ⊢ ƛ t ∈ Π A B

data _⊢_∈s_ where

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → ⋄ ⊢ [] ∈s Γ

  ⊢<,> : ∀ {m n Δ Γ A t} {γ : Sub m n}
         → Γ ⊢ γ ∈s Δ
         → Γ ⊢ A
         → Δ ⊢ t ∈ A [ γ ]
         → Γ ∙ A ⊢ (γ , t) ∈s Δ

getTy : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Tm n
getTy {A = A} _ = A

getTm : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Tm n
getTm {t = t} _ = t

dom : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ} → Γ ⊢ γ ∈s Δ → Ctx n
dom {Γ = Γ} _ = Γ

cod : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ} → Γ ⊢ γ ∈s Δ → Ctx m
cod {Δ = Δ} _ = Δ

wf⁻¹ : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢
wf⁻¹ (c-ext Γ⊢ _) = Γ⊢

wf⁻² : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢ A
wf⁻² (c-ext _ ⊢A) = ⊢A
