-------------------------------------------------------------------------------------------
--
-------------------------------------------------------------------------------------------
module Ext-Typed.DTyped.Preservation where

open import Function as F using (_$_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_] ; _∈_)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Ext-Typed.DTyped.Lambda

-------------------------------------------------------------------------------------------
-- Type system

-- Wellscoped contexts

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

lookup-ct : ∀ {n} (i : Fin n) (Γ : Ctx n) → Tm n
lookup-ct () ⋄
lookup-ct zero (Γ ∙ x) = wk x
lookup-ct (suc i) (Γ ∙ x) = wk $ lookup-ct i Γ

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _▹_⊢_

data _⊢    : ∀ {n} (Γ : Ctx n) → Set

data _⊢_   : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Tm n) (A : Tm n) → Set

data _▹_⊢_ : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) (γ : Sub m n) → Set

data _⊢ where

  c-emp : ⋄ ⊢

  c-ext : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢
          → Γ ⊢ A
          → Γ ∙ A ⊢

inv-ct : ∀ {n} {Γ : Ctx n} {A}
         → Γ ∙ A ⊢
         → Γ ⊢
inv-ct (c-ext Γ⊢ _) = Γ⊢

data _⊢_ where

  ty-U : ∀ {n} {Γ : Ctx n}
         → Γ ⊢
         → Γ ⊢ U         

  ty-w : ∀ {n} {Γ : Ctx n} {A}
         → Γ ⊢
         → Γ ⊢ A ∈ U
         → Γ ⊢ A

  ty-Π-F : ∀ {n} {Γ : Ctx n} {A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ Π A B

data _⊢_∈_ where

  tm-var : ∀ {n} {i : Fin n} {Γ : Ctx n}
           → Γ ⊢ var i ∈ lookup-ct i Γ

  tm-app : ∀ {n} {Γ : Ctx n} {f t A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ f ∈ Π A B
           → Γ ⊢ t ∈ A
           → Γ ⊢ f · t ∈ B [ id , t ]
           
  tm-Π-I : ∀ {n} {Γ : Ctx n}
             {A B t}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ∙ A ⊢ t ∈ B
           → Γ ⊢ ƛ t ∈ Π A B

data _▹_⊢_ where

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → Γ ▹ ⋄ ⊢ []

  ⊢<,> : ∀ {m n} {Γ : Ctx n}
           {Δ : Ctx m} {A t γ}
         → Γ ▹ Δ ⊢ γ
         → Δ ⊢ A
         → Γ ⊢ t ∈ A [ γ ]
         → Γ ▹ Δ ∙ A ⊢ (γ , t)

map-suc-pres : ∀ {m n Γ Δ A} (ρ : Ren m n) →
               Γ ⊢ A →
               Γ ▹ Δ ⊢ map var ρ →
               Γ ∙ A ▹ Δ ⊢ map var (map suc ρ)
map-suc-pres [] ⊢A (⊢<> x) = ⊢<> (c-ext x ⊢A)
map-suc-pres (x ∷ ρ) Γ⊢A' (⊢<,> ⊢ρ Δ⊢A ∈A[]) = ⊢<,> (map-suc-pres ρ Γ⊢A' ⊢ρ) Δ⊢A {!!}

↑-ren-pres : ∀ {m n Γ Δ A B} {ρ : Ren m n} →
             Γ ⊢ A →
             Δ ⊢ B →
             Γ ▹ Δ ⊢ map var ρ →
             Γ ∙ A ▹ Δ ∙ B ⊢ map var (↑-ren ρ)
↑-ren-pres ⊢A ⊢B ⊢ρ = ⊢<,> (map-suc-pres _ ⊢A ⊢ρ) ⊢B {!!}             

wk-preserves : ∀ {n Γ A B} {t : Tm n} →
               Γ ⊢ t ∈ A →
               Γ ∙ B ⊢ wk t ∈ wk A
wk-preserves t∈A = {!t∈A!}               

map-wk-preserves : ∀ {m n Γ Δ A} {ρ : Sub m n} →
                   Γ ⊢ A → Γ ▹ Δ ⊢ ρ → Γ ∙ A ▹ Δ ⊢ map wk ρ
map-wk-preserves ⊢A (⊢<> x) = ⊢<> (c-ext x ⊢A)
map-wk-preserves ⊢A (⊢<,> ⊢ρ Δ⊢A t∈) = ⊢<,> (map-wk-preserves ⊢A ⊢ρ) Δ⊢A {!!}

↑-pres : ∀ {m n Γ Δ A B} {ρ : Sub m n}  →
         Γ ⊢ A → Δ ⊢ B → Γ ▹ Δ ⊢ ρ →
         Γ ∙ A ▹ Δ ∙ B ⊢ ↑ ρ
↑-pres ⊢A ⊢B ⊢ρ = ⊢<,> (map-wk-preserves ⊢A ⊢ρ) ⊢B {!!}         

id-preserv : ∀ {n} {Γ : Ctx n} → Γ ⊢ → Γ ▹ Γ ⊢ id'
id-preserv {Γ = ⋄} Γ⊢ = ⊢<> Γ⊢
id-preserv {Γ = _ ∙ _} (c-ext Γ⊢ Γ⊢x) = ↑-pres Γ⊢x Γ⊢x (id-preserv Γ⊢)

lemma-3-1 : ∀ {m n} {Γ : Ctx n}
            {Δ : Ctx m} {ρ}
          → Δ ▹ Γ ⊢ ρ
          → Γ ⊢
lemma-3-1 (⊢<> Γ⊢) = c-emp
lemma-3-1 (⊢<,> ⊢ρ Γ⊢ _) = c-ext (lemma-3-1 ⊢ρ) Γ⊢

lemma-3-2 : ∀ {m n} {Γ : Ctx n}
            {Δ : Ctx m} {ρ}
          → Δ ▹ Γ ⊢ ρ
          → Δ ⊢
lemma-3-2 (⊢<> Δ⊢) = Δ⊢
lemma-3-2 (⊢<,> ⊢ρ _ _) = lemma-3-2 ⊢ρ          

lemma-1 : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ⊢
lemma-1 (ty-U Γ⊢)     = Γ⊢
lemma-1 (ty-w Γ⊢   _) = Γ⊢
lemma-1 (ty-Π-F ⊢A _) = lemma-1 ⊢A

p-preserv : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ∙ A ▹ Γ ⊢ p'
p-preserv ⊢A = map-wk-preserves ⊢A (id-preserv (lemma-1 ⊢A))

lookup-pres : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} i {ρ}
              → Δ ▹ Γ ⊢ ρ
              → Δ ⊢ lookup i ρ ∈ (lookup-ct i Γ [ ρ ])
lookup-pres zero    (⊢<,> ⊢ρ ⊢A t∈A[ρ]) = {!!}
lookup-pres (suc i) (⊢<,> ⊢ρ ⊢A t∈A[ρ]) = {!lookup-pres i ⊢ρ!}
                    

subst-lemma : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A t γ}
             → Δ ⊢ t ∈ A
             → Γ ▹ Δ ⊢ γ
             → Γ ⊢ t [ γ ] ∈ A [ γ ]
subst-lemma tm-var ⊢γ = {!!}
subst-lemma (tm-app ⊢A ⊢B f∈Π t∈A) ⊢γ = {!subst-lemma t∈A ⊢γ!}
subst-lemma (tm-Π-I ⊢A ⊢B t∈B) ⊢γ = {!subst-lemma t∈B (↑-pres ⊢γ!}             

{-
Goal: .Γ ⊢ (.f [ .γ ]) · (.t [ .γ ]) ∈ ((.B [ id , .t ]) [ .γ ])
Have: .Γ ⊢ .f [ .γ ] ∈ Π (.A [ .γ ]) (.B [ ↑ .γ ])
Have: .Γ ⊢ .t [ .γ ] ∈ (.A [ .γ ])
-}

comp-pres : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m}
              {Θ : Ctx k} {γ δ}
            → Γ ▹ Θ ⊢ γ
            → Δ ▹ Γ ⊢ δ
            → Δ ▹ Θ ⊢ γ ∘ δ
comp-pres (⊢<> _) ⊢δ = ⊢<> (lemma-3-2 ⊢δ)
comp-pres {Γ = Γ} {Δ = Δ} {Θ = Θ ∙ A} {γ = t ∷ γ} {δ}
          (⊢<,> ⊢γ ⊢A t∈A[γ]) ⊢δ = ⊢<,> (comp-pres ⊢γ ⊢δ) ⊢A (h (subst-lemma t∈A[γ] ⊢δ))
        where h : Δ ⊢ t [ δ ] ∈ (A [ γ ] [ δ ]) → Δ ⊢ t [ δ ] ∈ (A [ γ ∘ δ ])
              h hyp rewrite subComp A γ δ = hyp
  
