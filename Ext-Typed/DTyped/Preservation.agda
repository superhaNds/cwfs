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
lookup-ct zero    (Γ ∙ A) = wk A
lookup-ct (suc i) (Γ ∙ _) = wk $ lookup-ct i Γ

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

  ty-∈U : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢
          → Γ ⊢ A ∈ U
          → Γ ⊢ A

  ty-Π-F : ∀ {n} {Γ : Ctx n} {A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ Π A B

getTy : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Tm n
getTy {A = A} Γ⊢A = A

data _⊢_∈_ where
  tm-var : ∀ {n} {i : Fin n} {Γ : Ctx n}
           --→ Γ ⊢
           → Γ ⊢ var i ∈ lookup-ct i Γ

  tm-app : ∀ {n} {Γ : Ctx n} {f t A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ f ∈ Π A B
           → Γ ⊢ t ∈ A
           → Γ ⊢ f · t ∈ B [ id , t ]
           
  tm-Π-I : ∀ {n} {Γ : Ctx n} {A B t}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ∙ A ⊢ t ∈ B
           → Γ ⊢ ƛ t ∈ Π A B

data _▹_⊢_ where

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → Γ ▹ ⋄ ⊢ []

  ⊢<,> : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A t γ}
         → Γ ▹ Δ ⊢ γ
         → Δ ⊢ A
         → Γ ⊢ t ∈ A [ γ ]
         → Γ ▹ Δ ∙ A ⊢ (γ , t)

cod-sub : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ} → Γ ▹ Δ ⊢ ρ → Ctx m
cod-sub {Δ = Δ} _ = Δ

{-
lem : ∀ {m} {Γ : Ctx m} {x : Fin m} {n} {ρ : Vec (Fin m) n}
        {A : Tm n} {B : Tm m} →
      Γ ⊢ var x ∈ (A [ map var ρ ]) →
      Γ ∙ B ⊢ var (suc x) ∈ (A [ map var (map suc ρ) ])
lem varx∈ = {!!}       
-}
-- vr-wk-pr : ∀ {n} {Γ : Ctx n} {A}

map-suc-pres : ∀ {m n Γ Δ A} (ρ : Ren m n) →
               Γ ⊢ A →
               Γ ▹ Δ ⊢ map var ρ →
               Γ ∙ A ▹ Δ ⊢ map var (map suc ρ)
map-suc-pres [] ⊢A (⊢<> x) = ⊢<> (c-ext x ⊢A)
map-suc-pres {Γ = Γ} {A = A} (x ∷ ρ) Γ⊢A (⊢<,> ⊢ρ Δ⊢A' ∈A[])
  = ⊢<,> (map-suc-pres ρ Γ⊢A ⊢ρ) Δ⊢A' {!!}

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
map-wk-preserves ⊢A (⊢<,> ⊢ρ Δ⊢A t∈) = ⊢<,> (map-wk-preserves ⊢A ⊢ρ) Δ⊢A ({!wk-preserves t∈!})

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
lemma-1 (ty-∈U Γ⊢ _)   = Γ⊢
lemma-1 (ty-Π-F ⊢A _) = lemma-1 ⊢A

p-preserv : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ∙ A ▹ Γ ⊢ p'
p-preserv ⊢A = map-wk-preserves ⊢A (id-preserv (lemma-1 ⊢A))

lookup-pres : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} i {ρ}
              → Δ ▹ Γ ⊢ ρ
              → Δ ⊢ lookup i ρ ∈ (lookup-ct i Γ [ ρ ])
lookup-pres {Γ = Γ} {Δ} zero {ρ = t ∷ γ} (⊢<,> ⊢ρ ⊢A t∈A[ρ]) = lk1-h t∈A[ρ]
  where lk1-h : Δ ⊢ t ∈ (getTy ⊢A [ γ ])
                →  Δ ⊢ t ∈ (wk (getTy ⊢A) [ γ , t ])
        lk1-h hyp rewrite wk-sub-p {t = getTy ⊢A}
                        | sym $ subComp (getTy ⊢A) p (γ , t)
                        | pCons {t = t} γ = hyp
lookup-pres  {Γ = Γ} {Δ} (suc i) {ρ = t ∷ γ} (⊢<,> ⊢ρ ⊢A t∈A[ρ]) = lk2-h (lookup-pres i ⊢ρ)
  where lk2-h : Δ ⊢ lookup i γ ∈ (lookup-ct i (cod-sub ⊢ρ) [ γ ])
                → Δ ⊢ lookup i γ ∈ (wk (lookup-ct i (cod-sub ⊢ρ)) [ γ , t ])
        lk2-h hyp rewrite  wk-sub-p {t = lookup-ct i (cod-sub ⊢ρ)}
                         | sym $ subComp (lookup-ct i (cod-sub ⊢ρ)) p (γ , t)
                         | pCons {t = t} γ = hyp
                    

subst-lemma : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A t γ}
             → Δ ⊢ t ∈ A
             → Γ ▹ Δ ⊢ γ
             → Γ ⊢ t [ γ ] ∈ A [ γ ]
subst-lemma (tm-var {i = i} _)     ⊢γ = lookup-pres i ⊢γ
subst-lemma (tm-app ⊢A ⊢B f∈Π t∈A) ⊢γ = {!subst-lemma t∈A ⊢γ!}
subst-lemma (tm-Π-I ⊢A ⊢B t∈B)     ⊢γ = {!subst-lemma t∈B ?!}

-- B [ id , t ] [ γ ] ~ ƛ B · t
-- beta conversion?


{-
Goal: .Γ ⊢ (.f [ .γ ]) · (.t [ .γ ]) ∈ ((.B [ id , .t ]) [ .γ ])
Have: .Γ ⊢ .f [ .γ ] ∈ Π (.A [ .γ ]) (.B [ ↑ .γ ])
Have: .Γ ⊢ .t [ .γ ] ∈ (.A [ .γ ])
-}

ty-sub : ∀ {m n} {Δ : Ctx m}
             {Γ : Ctx n} {A γ}
          → Δ ⊢ A
          → Γ ▹ Δ ⊢ γ
          → Γ ⊢ A [ γ ]
ty-sub (ty-U x) ⊢γ = ty-U (lemma-3-2 ⊢γ)
ty-sub (ty-∈U Δ⊢ A∈U) ⊢γ = {!!}
ty-sub (ty-Π-F ⊢A ⊢B) ⊢γ = ty-Π-F (ty-sub ⊢A ⊢γ) {!!}          

{-
wkty : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ∙ A ⊢ wk A
wkty (ty-U x) = ty-U (c-ext x (ty-U x))
wkty (ty-w x x₁) = {!!}
wkty (ty-Π-F ⊢A ⊢A₁) = {!wkty ⊢A₁!}

q-pres : ∀ {n} {Γ : Ctx n} {A}
         → Γ ⊢ A
         → Γ ∙ A ⊢ q ∈ wk A
q-pres ⊢A = tm-var {!!}        
-}
tm-conv : ∀ {n} {Γ : Ctx n} {t A A'}
          → Γ ⊢ A'
          → Γ ⊢ t ∈ A
          → A' ≡ A
          → Γ ⊢ t ∈ A'
tm-conv _ t∈A refl = t∈A

lemma-4 : ∀ {n} {Γ : Ctx n} {A} {t} → Γ ⊢ t ∈ A → Γ ⊢ A
lemma-4 (tm-var ⊢lk) = ⊢lk
lemma-4 (tm-app x x₁ t∈A t∈ΠAB) = {!!} --ty-sub x₁ (⊢<,> {!id-preserv!} x (tm-conv (ty-sub x {!!}) t∈ΠAB {!!}))
lemma-4 (tm-Π-I x x₁ t∈A) = {!!}


comp-pres : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m}
              {Θ : Ctx k} {γ δ}
            → Γ ▹ Θ ⊢ γ
            → Δ ▹ Γ ⊢ δ
            → Δ ▹ Θ ⊢ γ ∘ δ
comp-pres (⊢<> _) ⊢δ = ⊢<> (lemma-3-2 ⊢δ)
comp-pres {Γ = Γ} {Δ = Δ} {Θ = Θ ∙ A} {γ = t ∷ γ} {δ}
          (⊢<,> ⊢γ ⊢A t∈A[γ]) ⊢δ
            = ⊢<,> (comp-pres ⊢γ ⊢δ) ⊢A (h (subst-lemma t∈A[γ] ⊢δ))
        where h : Δ ⊢ t [ δ ] ∈ (A [ γ ] [ δ ]) → Δ ⊢ t [ δ ] ∈ (A [ γ ∘ δ ])
              h hyp rewrite subComp A γ δ = hyp
