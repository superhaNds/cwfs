module ExtDepTyped.ImpSubTy where

open import Function as F using (_$_ ; flip)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_] ; _∈_)
open import Data.Vec.All as All using (All; []; _∷_)
open import Data.Vec.All.Properties using (gmap)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import ExtDepTyped.Raw.ImpSub
open import Unityped.ImpSub as Ren using (Ren)

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

wfTm-wf : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Γ ⊢
wfTm-wf (tm-var Γ⊢)       = Γ⊢
wfTm-wf (tm-app _ _ _ ⊢t) = wfTm-wf ⊢t
wfTm-wf (tm-Π-I ⊢A _ ⊢t)  = wf⁻¹ $ wfTm-wf ⊢t

wfSub-wf₁ : ∀ {m n Γ Δ} {γ : Sub m n} → Γ ⊢ γ ∈s Δ → Δ ⊢
wfSub-wf₁ (⊢<> Δ⊢)      = Δ⊢
wfSub-wf₁ (⊢<,> ⊢γ _ _) = wfSub-wf₁ ⊢γ

wfSub-wf₂ : ∀ {m n Γ Δ} {γ : Sub m n} → Γ ⊢ γ ∈s Δ → Γ ⊢
wfSub-wf₂ (⊢<> _)        = c-emp
wfSub-wf₂ (⊢<,> ⊢γ ⊢A _) = c-ext (wfSub-wf₂ ⊢γ) ⊢A

wfTy-wf : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A
          → Γ ⊢
            
wfTm-wfTy : ∀ {n} {Γ : Ctx n} {t A}
            → Γ ⊢ t ∈ A
            → Γ ⊢ A

wfTy-wf (ty-U Γ⊢)     = Γ⊢
wfTy-wf (ty-∈U ⊢A)    = wfTm-wf ⊢A
wfTy-wf (ty-Π-F ⊢A _) = wfTy-wf ⊢A

module Var where

  map-suc-preserv : ∀ {m n Γ Δ A} (ρ : Ren m n)
                    → Δ ⊢ A
                    → Γ ⊢ map var ρ ∈s Δ
                    → Γ ⊢ map var (map suc ρ) ∈s Δ ∙ A
  map-suc-preserv []      ⊢A  (⊢<> Γ⊢)       = ⊢<> (c-ext Γ⊢ ⊢A)
  map-suc-preserv (_ ∷ ρ) ⊢A' (⊢<,> ⊢ρ ⊢A _) = ⊢<,> (map-suc-preserv ρ ⊢A' ⊢ρ) ⊢A {!!}

wfTm-wfTy (tm-var Γ⊢)          = {!!}
wfTm-wfTy (tm-app ⊢A ⊢B ⊢f ⊢t) = {!!}
wfTm-wfTy (tm-Π-I ⊢A ⊢B _)     = ty-Π-F ⊢A ⊢B

  
