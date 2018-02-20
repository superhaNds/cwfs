module Ext-Typed.DTyped.LamPiSubTy where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat renaming (ℕ to Nat)
-- open import Data.Product hiding (_,_)
open import Data.Star using (Star; ε; _◅_)
open import Data.Unit
open import Function as F using (_$_)
open import Data.Vec as Vec hiding ([_] ; _∈_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Ext-Typed.DTyped.LamPiSub

-------------------------------------------------------------------------------------------
-- Type system

-- Wellscoped contexts

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

_,_ : ∀ {m n} → Sub Tm n m → Tm m → Sub Tm (suc n) m
σ , t = t ∷ σ

open TermSubst tmSubst hiding (var)

_[_] : {m n : Nat} → Tm m → Sub Tm m n → Tm n
_[_] = _/_

lookup-ct : ∀ {n} (i : Fin n) (Γ : Ctx n) → Tm n
lookup-ct zero    (Γ ∙ A) = weaken A
lookup-ct (suc i) (Γ ∙ _) = weaken $ lookup-ct i Γ

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _▹_⊢_

data _⊢    : ∀ {n} (Γ : Ctx n) → Set

data _⊢_   : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Tm n) (A : Tm n) → Set

data _▹_⊢_ : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) (γ : Sub Tm n m) → Set

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
           → Γ ⊢
           → Γ ⊢ var i ∈ lookup-ct i Γ

  tm-app : ∀ {n} {Γ : Ctx n} {f t A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ f ∈ Π A B
           → Γ ⊢ t ∈ A
           → Γ ⊢ (f · t) ∈ B [ id , t ]
           
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

getDom : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {γ} → Γ ▹ Δ ⊢ γ → Sub Tm m n
getDom {γ = γ} _ = γ

getTm : ∀ {n} {Γ : Ctx n} {t α} → Γ ⊢ t ∈ α → Tm n
getTm {t = t} _ = t

p : ∀ {n} → Sub Tm n (suc n)
p = wk

_∘_ : ∀ {m n k} → Sub Tm k n → Sub Tm n m → Sub Tm k m
_∘_ = _⊙_

sub-ctx-wf-1 : ∀ {n m Γ Δ} {ρ : Sub Tm n m}
               → Γ ▹ Δ ⊢ ρ
               → Δ ⊢
sub-ctx-wf-1 (⊢<> x) = c-emp
sub-ctx-wf-1 (⊢<,> ⊢ρ x x₁) = c-ext (sub-ctx-wf-1 ⊢ρ) x

sub-ctx-wf-2 : ∀ {n m Γ Δ} {ρ : Sub Tm n m}
               → Γ ▹ Δ ⊢ ρ
               → Γ ⊢
sub-ctx-wf-2 (⊢<> x) = x
sub-ctx-wf-2 (⊢<,> ⊢ρ x x₁) = sub-ctx-wf-2 ⊢ρ

lemma-wf : ∀ {n} {Γ : Ctx n} {A x}
           → Γ ∙ x ⊢ A
           → Γ ⊢ x
lemma-wf (ty-U  (c-ext _ x)) = x
lemma-wf (ty-∈U (c-ext _ x) _) = x
lemma-wf (ty-Π-F a _) = lemma-wf a           

wf-ty-ctx : ∀ {n} {Γ : Ctx n} {A}
            → Γ ⊢ A
            → Γ ⊢
wf-ty-ctx (ty-U x) = x
wf-ty-ctx (ty-∈U x _) = x
wf-ty-ctx (ty-Π-F ⊢A ⊢A₁) = wf-ty-ctx ⊢A            

postulate
  sub-lemma-ty : ∀ {m n} {Δ : Ctx m}
                  {Γ : Ctx n} {A γ}
                 → Δ ⊢ A
                 → Γ ▹ Δ ⊢ γ
                 → Γ ⊢ A [ γ ]

  sub-lemma-tm : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
                   {A t γ}
                 → Δ ⊢ t ∈ A
                 → Γ ▹ Δ ⊢ γ
                 → Γ ⊢ t [ γ ] ∈ A [ γ ]

module Var where

  var-suc : ∀ {m n Γ Δ A A'} i (ρ : Sub Fin n m)
            → Γ ⊢ var i ∈ (A [ map var ρ ])
            → Δ ⊢ A
            → Γ ▹ Δ ⊢ map var ρ
            → Γ ∙ A' ⊢ var (suc i) ∈ A [ map var (map suc ρ) ]
  var-suc {m} {n} i [] var∈ ⊢A (⊢<> x) = {!!}
  var-suc i (x ∷ ρ) var∈ ⊢A (⊢<,> ⊢ρ x₁ x₂) = {!!}            
  
  map-suc-pr : ∀ {m n Γ Δ A} (ρ : Sub Fin n m)
               → Γ ⊢ A
               → Γ ▹ Δ ⊢ Vec.map var ρ
               → Γ ∙ A ▹ Δ ⊢ Vec.map var (Vec.map suc ρ)
  map-suc-pr [] ⊢A (⊢<> Γ⊢) = ⊢<> (c-ext Γ⊢ ⊢A)
  map-suc-pr (i ∷ ρ) ⊢A (⊢<,> ⊢ρ Δ⊢A var∈) = ⊢<,> (map-suc-pr ρ ⊢A ⊢ρ) Δ⊢A ({!!})
 
  ↑-pr : ∀ {m n Γ Δ A A'} {ρ : Sub Fin m n}
         → Γ ⊢ A
         → Δ ⊢ A'
         → Γ ▹ Δ ⊢ Vec.map var ρ
         → Γ ∙ A ▹ Δ ∙ A' ⊢ Vec.map var (VarSubst._↑ ρ)
  ↑-pr ⊢A ⊢A' ⊢ρ = ⊢<,> (map-suc-pr _ ⊢A ⊢ρ) ⊢A' {!!}

  id-pr : ∀ {n} {Γ : Ctx n}
          → Γ ⊢
          → Γ ▹ Γ ⊢ Vec.map var VarSubst.id
  id-pr {Γ = ⋄} Γ⊢ = ⊢<> Γ⊢
  id-pr {Γ = Γ ∙ A} (c-ext Γ⊢ ⊢A) = ↑-pr ⊢A ⊢A (id-pr Γ⊢)

  wk-pr : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A
          → Γ ∙ A ▹ Γ ⊢ Vec.map var VarSubst.wk
  wk-pr ⊢A = map-suc-pr VarSubst.id ⊢A (id-pr (wf-ty-ctx ⊢A))

  lookup-pr : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} i ρ
              → Γ ▹ Δ ⊢ Vec.map var ρ
              → Γ ⊢ var (lookup i ρ) ∈ (lookup-ct i Δ [ Vec.map var ρ ])
  lookup-pr zero (x ∷ ρ) (⊢<,> ⊢ρ x₁ x₂) = {!!}
  lookup-pr (suc i) (x ∷ ρ) (⊢<,> ⊢ρ x₁ x₂) = {!!}

  []-pr : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {ρ : Sub Fin m n} {A t}
          → Γ ⊢ t ∈ A
          → Δ ▹ Γ ⊢ Vec.map var ρ
          → Δ ⊢ t /Var ρ ∈ A [ Vec.map var ρ ]
  []-pr (tm-var {i = i} x) ⊢ρ = lookup-pr i _ ⊢ρ
  []-pr (tm-app x x₁ ∈A ∈A₁) ⊢ρ = {!!}
  []-pr (tm-Π-I x x₁ ∈A) ⊢ρ = {!!}          

wk-pr : ∀ {n Γ A B} {t : Tm n}
        → Γ ⊢ A
        → Γ ⊢ t ∈ B
        → Γ ∙ A ⊢ weaken t ∈ weaken B
wk-pr ⊢A ∈B = {!!}

map-wk-pr : ∀ {m n Γ Δ A} {ρ : Sub Tm m n}
            → Γ ⊢ A
            → Γ ▹ Δ ⊢ ρ
            → Γ ∙ A ▹ Δ ⊢ Vec.map weaken ρ
map-wk-pr ⊢A (⊢<> x) = ⊢<> (c-ext x ⊢A)
map-wk-pr ⊢A (⊢<,> ⊢ρ x x₁) = ⊢<,> (map-wk-pr ⊢A ⊢ρ) x ({!!}) 

↑-pr : ∀ {m n Γ Δ A B} {ρ : Sub Tm m n}
       → Γ ⊢ A
       → Δ ⊢ B
       → Γ ▹ Δ ⊢ ρ
       → Γ ∙ A ▹ Δ ∙ B ⊢ ρ ↑ 
↑-pr ⊢A ⊢B ⊢ρ = ⊢<,> (map-wk-pr ⊢A ⊢ρ) ⊢B {!!}

id-pr : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → Γ ▹ Γ ⊢ id
id-pr {Γ = ⋄}     Γ⊢            = ⊢<> Γ⊢
id-pr {Γ = Γ ∙ x} (c-ext Γ⊢ ⊢x) = ↑-pr ⊢x ⊢x (id-pr Γ⊢)

p-pr : ∀ {n A} {Γ : Ctx n}
       → Γ ⊢ A
       → Γ ∙ A ▹ Γ ⊢ p
p-pr {Γ = ⋄}     ⊢A = ⊢<> (c-ext c-emp ⊢A)
p-pr {Γ = Γ ∙ x} ⊢A =
  map-wk-pr ⊢A (↑-pr (lemma-wf ⊢A) (lemma-wf ⊢A)
               (id-pr (wf-ty-ctx (lemma-wf ⊢A))))

⊢var₀ : ∀ {n A} {Γ : Ctx n} → Γ ∙ A ⊢ var zero ∈ A [ p ]
⊢var₀ {A = A} {Γ} = {!A!}

lemma-ty : ∀ {m n} {Δ : Ctx m}
             {Γ : Ctx n} {A γ}
           → Δ ⊢ A
           → Γ ▹ Δ ⊢ γ
           → Γ ⊢ A [ γ ]
lemma-ty (ty-U x) ⊢γ = ty-U (sub-ctx-wf-2 ⊢γ)
lemma-ty (ty-∈U Δ⊢ A∈U) ⊢γ = ty-∈U (sub-ctx-wf-2 ⊢γ) (sub-lemma-tm A∈U ⊢γ)
lemma-ty (ty-Π-F ⊢A ⊢B) ⊢γ = ty-Π-F (lemma-ty ⊢A ⊢γ) {!!}

testl : ∀ {n m} (γ : Sub Tm m n) t B
        → B [ (id , t) ] [ γ ] ≡ (B [ (γ ↑) ]) [ (id , (t [ γ ])) ]
testl = {!!}        

lemma-tm : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
             {A t γ}
           → Δ ⊢ t ∈ A
           → Γ ▹ Δ ⊢ γ
           → Γ ⊢ t [ γ ] ∈ A [ γ ]
lemma-tm (tm-var x) ⊢γ = {!!}
lemma-tm (tm-app ⊢A ⊢B f∈Π t∈A) ⊢γ
  rewrite testl (getDom ⊢γ) (getTm t∈A) (getTy ⊢B)
    = tm-app (lemma-ty ⊢A ⊢γ) {!!} (lemma-tm f∈Π ⊢γ) (lemma-tm t∈A ⊢γ)
lemma-tm (tm-Π-I x x₁ t∈A) ⊢γ = {!!}           
