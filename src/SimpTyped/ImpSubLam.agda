module SimpTyped.ImpSubLam  where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec as Vec hiding ([_] ; lookup)
open import Data.Fin hiding (lift)
open import Data.Product hiding (<_,_> ; map)
open import Relation.Binary.PropositionalEquality  hiding ([_] ; cong-∘)
open import Function as F using (_$_ ; flip)
open import Relation.Binary using (Setoid ; IsEquivalence)
open ≡-Reasoning
open import SimpTyped.Scwf
open import SimpTyped.Type renaming (⋄ to ε)

infix 12 _/_
infix 12 _[_]

infix 8 _∘ᵣ_
infix 8 _∘_
infix 8 _∘r_
infix 8 _r∘_

-- Variables are well-scoped, natural number with a proof of existence in context

Var : ∀ {n} (Γ : Ctx n) (A : Ty) → Set
Var Γ A = Σ (Fin _) (λ i → Vec.lookup Γ i ≡ A)

-- STLC terms

data Tm {n} (Γ : Ctx n) : Ty → Set where
  var : ∀ {A}
        → Var Γ A
        ----------
        → Tm Γ A
        
  ƛ : ∀ {A B}
      → Tm (Γ ∙ A) B
      --------------
      → Tm Γ (A ⇒ B)
        
  app : ∀ {A B}
        → Tm Γ (A ⇒ B)
        → Tm Γ A
        --------------
        → Tm Γ B

-- Generalized substitution to work with renamings too

data Subst {m} (T : ∀ {k} → Ctx k → Ty → Set) (Δ : Ctx m) : ∀ {n} (Γ : Ctx n) → Set where
  <> : Subst T Δ ε
  
  <_,_> : ∀ {n A} {Γ : Ctx n}
          → Subst T Δ Γ
          → T Δ A
          --------------
          → Subst T Δ (Γ ∙ A)

Sub : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) → Set
Sub Δ Γ = Subst Tm Δ Γ

Ren : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) → Set
Ren Δ Γ = Subst Var Δ Γ

-- Conor's kit from Type preserving renaming and substitution
-- Helps with transitioning between renamings and substitutions in proofs

record SubstTemp (T : ∀ {n} → Ctx n → Ty → Set) : Set where
  field
    vr : ∀ {n A} {Γ : Ctx n} → Var Γ A → T Γ A
    tm : ∀ {n A} {Γ : Ctx n} → T Γ A → Tm Γ A
    wk : ∀ {n A B} {Γ : Ctx n} → T Γ A → T (Γ ∙ B) A

record SubstTemp⁺ (T : ∀ {n} → Ctx n → Ty → Set) : Set where
  field
    temp : SubstTemp T
    sub  : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} → T Δ A → Subst T Γ Δ → T Γ A

-- Weaken an arbitrary substitution

++ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {T : ∀ {k} → Ctx k → Ty → Set}
     → Subst T Δ Γ → SubstTemp T → Subst T (Δ ∙ A) Γ
++ <>        _  = <>
++ < γ , x > st = < ++ γ st , SubstTemp.wk st x >

-- lift an arbitrary substitution

lift : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {T : ∀ {k} → Ctx k → Ty → Set}
       → Subst T Δ Γ → SubstTemp T → Subst T (Δ ∙ A) (Γ ∙ A)
lift γ st = < ++ γ st , SubstTemp.vr st (zero , refl) >

-- Scfw at the var level only with renamings

module Ren where

  q : ∀ {n A} {Γ : Ctx n} → Var (Γ ∙ A) A
  q = (zero , refl)

  weaken : ∀ {A A' m} {Γ : Ctx m}
           → Var Γ A
           → Var (Γ ∙ A') A
  weaken (i , refl) = (suc i , refl)

  infixl 20 _/_

  _/_ : ∀ {m n} {A : Ty} {Δ : Ctx m} {Γ : Ctx n}
          {T : ∀ {k} → Ctx k → Ty → Set}
        → Var Γ A → Subst T Δ Γ → T Δ A
  _/_ (() , _)       <>
  _/_ (zero , refl)  < _ , t > = t
  _/_ (suc i , refl) < γ , _ > = (i , refl) / γ         

  VarTemp : SubstTemp Var
  VarTemp = record { vr = λ x → x ; tm = var ; wk = weaken }

  VarTemp⁺ : SubstTemp⁺ Var
  VarTemp⁺ = record { temp = VarTemp ; sub = _/_ }

  ↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} → Ren Δ Γ → Ren (Δ ∙ A) (Γ ∙ A)
  ↑ ρ = lift ρ VarTemp

  id : ∀ {n} {Γ : Ctx n} → Ren Γ Γ
  id {Γ = []}    = <>
  id {Γ = _ ∷ Γ} = ↑ id

  p : ∀ {n A} {Γ : Ctx n} → Ren (Γ ∙ A) Γ
  p = ++ id VarTemp

open Ren using (VarTemp ; VarTemp⁺)

pᵣ : ∀ {n A} {Γ : Ctx n} → Ren (Γ ∙ A) Γ
pᵣ = Ren.p

idᵣ : ∀ {n} {Γ : Ctx n} → Ren Γ Γ
idᵣ = Ren.id

++ᵣ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} → Ren Δ Γ → Ren (Δ ∙ A) Γ
++ᵣ ρ = ++ ρ VarTemp

renToSub : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → Ren Δ Γ → Sub Δ Γ
renToSub <>        = <>
renToSub < ρ , x > = < renToSub ρ , var x >

subTm : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {T : ∀ {k} → Ctx k → Ty → Set}
        → SubstTemp T → Tm Γ A → Subst T Δ Γ → Tm Δ A
subTm st (var x)   γ = SubstTemp.tm st (x Ren./ γ)
subTm st (ƛ t)     γ = ƛ (subTm st t (lift γ st))
subTm st (app f t) γ = app (subTm st f γ) (subTm st t γ)        

_/_ : ∀ {m n} {A : Ty} {Δ : Ctx m} {Γ : Ctx n} → Tm Γ A → Ren Δ Γ → Tm Δ A
t / γ = subTm VarTemp t γ

weaken : ∀ {n A A'} {Γ : Ctx n} → Tm Γ A → Tm (Γ ∙ A') A
weaken t = t / Ren.p

TmTemp : SubstTemp Tm
TmTemp = record { vr = var ; tm = λ x → x ; wk = weaken }

++ₜ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} → Sub Δ Γ → Sub (Δ ∙ A) Γ
++ₜ γ = ++ γ TmTemp

q : ∀ {n A} {Γ : Ctx n} → Tm (Γ ∙ A) A
q = var Ren.q

↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} → Sub Δ Γ → Sub (Δ ∙ A) (Γ ∙ A)
↑ γ = lift γ TmTemp

id : ∀ {n} {Γ : Ctx n} → Sub Γ Γ
id  = renToSub Ren.id

p : ∀ {n A} {Γ : Ctx n} → Sub (Γ ∙ A) Γ
p = renToSub Ren.p

_[_] : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} → Tm Γ A → Sub Δ Γ → Tm Δ A
t [ γ ] = subTm TmTemp t γ

TmTemp⁺ : SubstTemp⁺ Tm
TmTemp⁺ = record { temp = TmTemp ; sub = _[_] }

comp : ∀ {k m n} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} {T : ∀ {h} → Ctx h → Ty → Set}
       → SubstTemp⁺ T → Subst T Δ Γ → Subst T E Δ → Subst T E Γ
comp st <>        γ' = <>
comp st < γ , x > γ' = < comp st γ γ' , SubstTemp⁺.sub st x γ' >

_∘ᵣ_ : ∀ {k m n} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} → Ren Δ Γ → Ren E Δ → Ren E Γ
ρ ∘ᵣ ρ' = comp VarTemp⁺ ρ ρ'       

_∘_ : ∀ {k m n} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} → Sub Δ Γ → Sub E Δ → Sub E Γ
γ ∘ γ' = comp TmTemp⁺ γ γ'

_∘r_ : ∀ {k m n} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} → Sub Δ Γ → Ren E Δ → Sub E Γ
<>        ∘r ρ = <>
< γ , t > ∘r ρ = < γ ∘r ρ , t / ρ >

_r∘_ : ∀ {k m n} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} → Ren Δ Γ → Sub E Δ → Sub E Γ
<>        r∘ γ = <>
< ρ , x > r∘ γ = < ρ r∘ γ , x Ren./ γ >

cong-ren : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {x₁ x₂ : Var Γ A} {ρ₁ ρ₂ : Ren Δ Γ}
           → x₁ ≡ x₂ → ρ₁ ≡ ρ₂ → x₁ Ren./ ρ₁ ≡ x₂ Ren./ ρ₂
cong-ren = cong₂ Ren._/_          

cong-sub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t₁ t₂ : Tm Γ A} {γ₁ γ₂ : Sub Δ Γ}
           → t₁ ≡ t₂ → γ₁ ≡ γ₂ → t₁ [ γ₁ ] ≡ t₂ [ γ₂ ]
cong-sub = cong₂ _[_]

cong-ext : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t₁ t₂ : Tm Δ A} {γ₁ γ₂ : Sub Δ Γ}
           → γ₁ ≡ γ₂ → t₁ ≡ t₂ → < γ₁ , t₁ > ≡ < γ₂ , t₂ >
cong-ext = cong₂ <_,_>           

cong-∘ : ∀ {k m n} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} {γ₁ γ₂ : Sub Δ Γ} {δ₁ δ₂ : Sub E Δ}
         → γ₁ ≡ γ₂ → δ₁ ≡ δ₂ → γ₁ ∘ δ₁ ≡ γ₂ ∘ δ₂
cong-∘ refl refl = refl         

wk-ren-eq : ∀ {m n A B} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) (x : Var Γ A)
            → x Ren./ (++ {A = B} ρ VarTemp) ≡ Ren.weaken (x Ren./ ρ)
wk-ren-eq <>        (()    , _)
wk-ren-eq < _ , _ > (zero  , refl) = refl
wk-ren-eq < ρ , _ > (suc i , refl) = wk-ren-eq ρ (i , refl)            

renId : ∀ {n A} {Γ : Ctx n} (x : Var Γ A) → (Ren._/_){Δ = Γ} x Ren.id ≡ x
renP : ∀ {n A B} {Γ : Ctx n} (x : Var Γ A) → (Ren._/_) {Γ = Γ} x (Ren.p {A = B}) ≡ Ren.weaken x

renId {Γ = []}    (()    , _)
renId {Γ = _ ∷ _} (zero  , refl) = refl
renId {Γ = _ ∷ _} (suc i , refl) = renP (i , refl)

renP {Γ = Γ} x = trans (wk-ren-eq Ren.id x) (cong Ren.weaken (renId {Γ = Γ} x))

wk-ext-ren : ∀ {m n A A'} {Δ : Ctx m} {Γ : Ctx n} {ρ : Ren Δ Γ} {y : Var Γ A} {x : Var Δ A'}
             → (Ren.weaken y) Ren./ < ρ , x > ≡ y Ren./ ρ
wk-ext-ren {ρ = <>}        {()    , _}
wk-ext-ren {ρ = < _ , _ >} {zero  , refl} = refl
wk-ext-ren {ρ = < _ , _ >} {suc _ , refl} = refl

wk-ext-ren' : ∀ {m n A A'} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} {x : Var Γ A} {t : Tm Δ A'}
              → (Ren.weaken x) Ren./ < γ , t > ≡ x Ren./ γ
wk-ext-ren' {γ = <>}        {()    , _}
wk-ext-ren' {γ = < _ , _ >} {zero  , refl} = refl
wk-ext-ren' {γ = < _ , _ >} {suc _ , refl} = refl             

ren-comp-++ : ∀ {k m n A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
                {ρ' : Ren Γ E} {ρ} {x : Var Δ A}
              →  (_∘ᵣ_ {E = Δ}) (++ᵣ ρ') (< ρ , x >) ≡ ρ' ∘ᵣ ρ
ren-comp-++ {ρ' = <>}         {ρ} = refl
ren-comp-++ {ρ' = < ρ' , x >} {ρ} = cong₂ <_,_> ren-comp-++ (wk-ext-ren {ρ = ρ})

ren-sub-comp++ : ∀ {k m n A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
                 {ρ : Ren Γ E} {γ : Sub Δ Γ} {x : Tm Δ A}
                 → ++ᵣ ρ r∘ < γ , x > ≡ ρ r∘ γ
ren-sub-comp++ {ρ = <>}            = refl
ren-sub-comp++ {ρ = < ρ , x >} {γ} = cong₂ <_,_> ren-sub-comp++ (wk-ext-ren' {γ = γ} )

renIdR : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ρ ∘ᵣ Ren.id ≡ ρ
renIdR {Δ = Δ} <>        = refl
renIdR {Δ = Δ} < ρ , x > = cong₂ <_,_> (renIdR ρ) (renId {Γ = Δ} x)

renExtId : ∀ {n A} {Γ : Ctx n} → Ren.id {Γ = Γ ∙ A} ≡ < Ren.p , Ren.q  >
renExtId = refl

ren-qSub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n}
             {ρ : Ren Δ Γ} {x : Var Δ A}
           → Ren.q Ren./ < ρ , x > ≡ x
ren-qSub = refl

renPcomp : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {ρ : Ren Δ Γ} {x : Var Δ A} → Ren.p ∘ᵣ < ρ , x > ≡ ρ
renIdL : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → Ren.id ∘ᵣ ρ ≡ ρ

renPcomp = trans ren-comp-++ (renIdL _)

renIdL <>        = refl
renIdL < ρ , x > = cong₂ <_,_> renPcomp refl

ren-assoc : ∀ {k m n A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
              {ρ : Ren Γ E} {ρ' : Ren Δ Γ} {x : Var E A}
              → x Ren./ ρ Ren./ ρ' ≡ x Ren./ (ρ ∘ᵣ ρ')
ren-assoc {ρ = <>}        {_}  {()    , _}
ren-assoc {ρ = < ρ , x >} {_}  {zero  , refl} = refl
ren-assoc {ρ = < ρ , x >} {ρ'} {suc i , refl} = ren-assoc {ρ = ρ} {x = (i , refl) }

∘ᵣ-assoc : ∀ {j k m n} {Ζ : Ctx j} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
             {ρ₁ : Ren E Ζ } {ρ₂ : Ren Γ E } {ρ₃ : Ren Δ Γ }
           → ρ₁ ∘ᵣ (ρ₂ ∘ᵣ ρ₃) ≡ (ρ₁ ∘ᵣ ρ₂) ∘ᵣ ρ₃
∘ᵣ-assoc {ρ₁ = <>}                   = refl
∘ᵣ-assoc {ρ₁ = < ρ₁ , x >} {ρ₂} {ρ₃} = cong₂ <_,_> (∘ᵣ-assoc {ρ₁ = ρ₁} {ρ₂}) (sym $ ren-assoc {ρ = ρ₂} {x = x})

substWeakRen : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ++ₜ {A = A} (renToSub ρ) ≡ renToSub (++ᵣ ρ)
substWeakRen <>        = refl
substWeakRen < ρ , x > = cong₂ <_,_> (substWeakRen ρ) (cong var (renP x))

↑id-id : ∀ {n A} {Γ : Ctx n} → ↑ {A = A} {Γ} id ≡ id
↑id-id = cong₂ <_,_> (substWeakRen Ren.id) refl

subRen : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n}
         (t : Tm Γ A) (ρ : Ren Δ Γ) → t [ renToSub ρ ] ≡ t / ρ
subRen (var (()    , _))    <>
subRen (var (zero  , refl)) < ρ , _ > = refl
subRen (var (suc i , refl)) < ρ , _ > = subRen (var (i , refl)) ρ
subRen (app f t) ρ = cong₂ app (subRen f ρ) (subRen t ρ)
subRen (ƛ t) ρ =
  cong ƛ (trans
           (cong-sub {t₁ = t} refl
             (cong₂ <_,_> (substWeakRen ρ) refl))
           (subRen t (lift ρ VarTemp)))

renTmId : ∀ {n A} {Γ : Ctx n} (t : Tm Γ A) → t / Ren.id ≡ t
renTmId {Γ = Γ} (var x)   = cong var (renId {Γ = Γ} x)
renTmId         (ƛ t)     = cong ƛ (renTmId t)
renTmId         (app f t) = cong₂ app (renTmId f) (renTmId t)

sub-p-wk : ∀ {n A A'} {Γ : Ctx n} (t : Tm Γ A) → t [ p {A = A'} ] ≡ weaken t
sub-p-wk t = trans (subRen t Ren.p) refl

∘ᵣ-p-wk : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ρ ∘ᵣ Ren.p {A = A} ≡ ++ᵣ ρ
∘ᵣ-p-wk <>        = refl
∘ᵣ-p-wk < ρ , x > = cong₂ <_,_> (∘ᵣ-p-wk ρ) (renP x)

∘-p-wk : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub Δ Γ) → γ ∘ p {A = A} ≡ ++ₜ γ
∘-p-wk <>        = refl
∘-p-wk < γ , t > = cong₂ <_,_> (∘-p-wk γ) (sub-p-wk t)

p-∘ᵣ-↑ : ∀ {m n} {A : Ty} {Δ : Ctx m} {Γ : Ctx n} (σ : Ren Δ Γ)→ Ren.p {A = A} ∘ᵣ (Ren.↑ σ) ≡ ++ᵣ σ
p-∘ᵣ-↑ σ = trans
  (ren-comp-++ {ρ' = Ren.id} {++ᵣ σ} {Ren.q})
  (renIdL (++ᵣ σ))

∘ᵣ-p : ∀ {m n} {A : Ty} {Δ : Ctx m} {Γ : Ctx n} (σ : Ren Δ Γ) → σ ∘ᵣ Ren.p ≡ Ren.p ∘ᵣ (Ren.↑ {A = A} σ)
∘ᵣ-p {A = A} σ rewrite p-∘ᵣ-↑ {A = A} σ = ∘ᵣ-p-wk σ

auxlemm₁ : ∀ {k m n A B} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) (σ : Ren E Δ) (x : Var E B)
           → (++ᵣ ρ) ∘ᵣ (Ren.↑ {A = A} σ) ≡ ++ᵣ (++ᵣ ρ) ∘ᵣ < < ++ᵣ σ , Ren.weaken x > , Ren.q >
auxlemm₁ <>        _ _ = refl
auxlemm₁ < ρ , y > σ x = cong₂ <_,_> (auxlemm₁ ρ σ x) (sym $ begin
  Ren.weaken (Ren.weaken y) Ren./
    < < ++ᵣ σ , Ren.weaken x > , Ren.q >        ≡⟨ wk-ext-ren {ρ = < ++ᵣ σ , Ren.weaken x >} {Ren.weaken y} ⟩
  (Ren.weaken y) Ren./ < ++ᵣ σ , Ren.weaken x > ≡⟨ wk-ext-ren {ρ = ++ᵣ σ} ⟩
  y Ren./ ++ᵣ σ                                 ≡⟨ sym $ wk-ext-ren {ρ = ++ᵣ σ} ⟩
  Ren.weaken y Ren./ Ren.↑ σ
  ∎)

-- Scfw law: substitution in id ------------------------------------------------
subId : ∀ {n A} {Γ : Ctx n} (t : Tm Γ A) → t [ id ] ≡ t
subId t = trans (subRen t Ren.id) (renTmId t)

-- Scfw law: id on the right --------------------------------------------------
idR : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → γ ∘ id ≡ γ
idR {γ = <>}        = refl
idR {γ = < γ , t >} = cong₂ <_,_> idR (subId t)

wk-∘-↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ++ᵣ {A = A} ρ ≡ Ren.p ∘ᵣ Ren.↑ ρ
wk-∘-↑ <>        = refl
wk-∘-↑ < ρ , x > = cong (<_, Ren.weaken x >) (trans (wk-∘-↑ ρ) (auxlemm₁ Ren.id ρ x))

p-↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ρ ∘ᵣ Ren.p {A = A} ≡ Ren.p ∘ᵣ Ren.↑ ρ
p-↑ ρ = trans (∘ᵣ-p-wk ρ) (wk-∘-↑ ρ)

ren2Sub-r∘ : ∀ {m n k} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k} (ρ : Ren Δ Γ) (γ : Sub E Δ) → (renToSub ρ) ∘ γ ≡ ρ r∘ γ
ren2Sub-r∘ <>        γ = refl
ren2Sub-r∘ < ρ , x > γ = cong (<_, x Ren./ γ >) (ren2Sub-r∘ ρ γ)

p-r∘-id : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub Δ Γ) (t : Tm Δ A) → Ren.p r∘ < γ , t > ≡ Ren.id r∘ γ
p-r∘-id γ t = ren-sub-comp++

p-r∘-idL : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub Δ Γ) → Ren.id r∘ γ ≡ γ
p-r∘-sub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub Δ Γ) (t : Tm Δ A) → Ren.p r∘ < γ , t > ≡ γ

p-r∘-idL <>        = refl
p-r∘-idL < γ , x > = cong <_, x > (p-r∘-sub γ _)

p-r∘-sub t γ = trans ren-sub-comp++ (p-r∘-idL t)

wk-var : ∀ {n A B} {Γ : Ctx n} {x : Var Γ A} → var (Ren.weaken {A' = B} {Γ = Γ} x) ≡ weaken (var x)
wk-var {A = A} {B} {Γ} {x}
  rewrite renP {B = B} {Γ} x = refl

++-renSub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → renToSub (++ᵣ {A = A} ρ) ≡ ++ₜ (renToSub ρ)
++-renSub <>        = refl
++-renSub < ρ , x > = cong₂ <_,_> (++-renSub ρ) wk-var

-- Scfw law: first projection ----------------------------------------------------------
p-∘-sub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} {t : Tm Δ A} → p ∘ < γ , t > ≡ γ
p-∘-sub {A = A} {Γ = Γ} {γ} {t} = begin
  p ∘ < γ , t >       ≡⟨ ren2Sub-r∘ Ren.p < γ , t > ⟩
  Ren.p r∘ < γ , t >  ≡⟨ p-r∘-id γ t ⟩
  Ren.id r∘ γ         ≡⟨ p-r∘-idL γ ⟩
  γ ∎

-- Scfw law: id on the left --------------------------------------------
idL : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → id ∘ γ ≡ γ
idL {γ = <>}        = refl
idL {γ = < γ , t >} = cong <_, t > p-∘-sub

ren-/-↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) (x : Var Γ A)
          → Ren.weaken {A' = A} (x Ren./ ρ) ≡ (Ren.weaken x) Ren./ (Ren.↑ ρ)
ren-/-↑ < _ , _ > (zero , refl)  = refl
ren-/-↑ < ρ , _ > (suc y , refl) = ren-/-↑ ρ (y , refl)

wk-dist-right : ∀ {m n k A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
        → (ρ : Ren Γ E) (ρ' : Ren Δ Γ)
        → ρ ∘ᵣ ++ᵣ ρ' ≡ ++ᵣ {A = A} (ρ ∘ᵣ ρ')
wk-dist-right <>        ρ' = refl
wk-dist-right < ρ , x > ρ' = cong₂ <_,_> (wk-dist-right ρ ρ') (wk-ren-eq ρ' x)

ren↑-dist : ∀ {k m n A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
            (ρ : Ren Γ E) (ρ' : Ren Δ Γ)
            → Ren.↑ {A = A} ρ ∘ᵣ Ren.↑ ρ' ≡ Ren.↑ (ρ ∘ᵣ ρ')
ren↑-dist ρ ρ' = let v = (zero , refl) in begin
  < ++ᵣ ρ ∘ᵣ < ++ᵣ ρ' , v > , v > ≡⟨ cong <_, v > (ren-comp-++ {ρ' = ρ} {++ᵣ ρ'}) ⟩
  < ρ ∘ᵣ ++ᵣ ρ' , v >             ≡⟨ cong <_, v > (wk-dist-right ρ ρ') ⟩
  < ++ᵣ (ρ ∘ᵣ ρ') , v >           ≡⟨⟩
  Ren.↑ (ρ ∘ᵣ ρ')
  ∎

/-assoc : ∀ {k m n A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
            {ρ : Ren Γ E} {ρ' : Ren Δ Γ} {t : Tm E A}
          → (t / ρ) / ρ' ≡ t / (ρ ∘ᵣ ρ')
/-assoc {ρ = ρ} {ρ'} {var x}   = cong var (ren-assoc {ρ = ρ})
/-assoc {ρ = ρ} {ρ'} {app f t} = cong₂ app (/-assoc {t = f}) (/-assoc {t = t})
/-assoc {ρ = ρ} {ρ'} {ƛ t}     = cong ƛ $ begin
  (t / Ren.↑ ρ) / Ren.↑ ρ'  ≡⟨ /-assoc {ρ = Ren.↑ ρ} {ρ' = Ren.↑ ρ'} {t = t} ⟩
  t / (Ren.↑ ρ ∘ᵣ Ren.↑ ρ') ≡⟨ cong (t /_) (ren↑-dist ρ ρ') ⟩ 
  t / Ren.↑ (ρ ∘ᵣ ρ') ∎  

/-p-↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) (t : Tm Γ A)
      → (t / ρ) / Ren.p {A = A} ≡ (t / Ren.p) / (Ren.↑ ρ)
/-p-↑ ρ t = begin
  (t / ρ) / Ren.p        ≡⟨ /-assoc {ρ = ρ} {Ren.p} {t} ⟩
  t / (ρ ∘ᵣ Ren.p)       ≡⟨ cong (t /_) (∘ᵣ-p ρ) ⟩
  t / (Ren.p ∘ᵣ Ren.↑ ρ) ≡⟨ sym $ /-assoc {ρ = Ren.p} {Ren.↑ ρ} {t} ⟩
  (t / Ren.p) / Ren.↑ ρ  ∎

wk-tm-ren : ∀ {m n A A'} {Δ : Ctx m} {Γ : Ctx n}
            (t : Tm Δ A) (ρ : Ren Γ Δ) (x : Var Γ A')
            → weaken t / < ρ , x > ≡ t / ρ
wk-tm-ren t ρ x = begin
  weaken t / < ρ , x >     ≡⟨ cong (_/ < ρ , x >) (sym $ sub-p-wk t) ⟩
  (t [ p ]) / < ρ , x >    ≡⟨ cong (_/ < ρ , x >) (subRen t Ren.p) ⟩
  (t / Ren.p) / < ρ , x >  ≡⟨ /-assoc {ρ = Ren.p} {< ρ , x >} {t} ⟩
  t / (Ren.p ∘ᵣ < ρ , x >) ≡⟨ cong (t /_) (renPcomp) ⟩
  t / ρ ∎

sub-comp++ : ∀ {k m n A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
             (σ : Sub Γ E) (ρ : Ren Δ Γ) (x : Var Δ A)
             → ++ₜ σ ∘r < ρ , x > ≡ σ ∘r ρ
sub-comp++ <>        ρ x = refl
sub-comp++ < σ , t > ρ x = cong₂ <_,_> (sub-comp++ σ ρ x) (wk-tm-ren t ρ x)

r∘-assoc : ∀ {m n k A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
             (y : Var Γ A) (ρ : Ren Δ Γ) (σ : Sub E Δ)
           → (y Ren./ ρ) Ren./ σ ≡ y Ren./ (ρ r∘ σ)
r∘-assoc (zero  , refl) < ρ , x > σ = refl
r∘-assoc (suc i , refl) < ρ , x > σ = r∘-assoc (i , refl) ρ σ

sub-comp++r : ∀ {k m n A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
               (ρ : Ren Γ E) (σ : Sub Δ Γ) (x : Tm Δ A)
              → ++ᵣ ρ r∘ < σ , x > ≡ ρ r∘ σ             
sub-comp++r <>         _ _ = refl
sub-comp++r < ρ , y > σ x = cong₂ <_,_> (sub-comp++r ρ σ x) (begin
  Ren.weaken y Ren./ < σ , x >    ≡⟨ cong (λ a → a Ren./ < σ , x >) (sym $ renP y) ⟩
  (y Ren./ Ren.p) Ren./ < σ , x > ≡⟨ r∘-assoc y Ren.p < σ , x > ⟩
  y Ren./ (Ren.p r∘ < σ , x >)    ≡⟨ cong (y Ren./_) (p-r∘-sub σ x) ⟩
  y Ren./ σ
  ∎)

weaken-/ : ∀ {m n A A'} {Δ : Ctx m} {Γ : Ctx n} (t : Tm Δ A) (ρ : Ren Γ Δ)
           → weaken {A' = A'} (t / ρ) ≡ t / (++ᵣ ρ)
weaken-/ t ρ = begin
  weaken (t / ρ)         ≡⟨ sym $ sub-p-wk (t / ρ) ⟩
  (t / ρ) [ p ]          ≡⟨ subRen (t / ρ) Ren.p ⟩
  (t / ρ) / Ren.p        ≡⟨ /-assoc {ρ = ρ} {Ren.p} {t} ⟩
  t / (ρ ∘ᵣ Ren.p)       ≡⟨ cong (t /_) (p-↑ ρ) ⟩
  t / (Ren.p ∘ᵣ Ren.↑ ρ) ≡⟨ (sym $ cong (t /_) (wk-∘-↑ ρ)) ⟩
  t / ++ᵣ ρ
  ∎

ren-/-assoc : ∀ {k m n A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
                (x : Var Γ A) (σ : Sub Δ Γ) (γ : Sub E Δ)
              → (x Ren./ σ) [ γ ] ≡ x Ren./ (σ ∘ γ)
ren-/-assoc (zero  , refl) < σ , x > γ = refl
ren-/-assoc (suc i , refl) < σ , x > γ = ren-/-assoc (i , refl) σ γ

weaken-ren-/ : ∀ {m n A A'} {Δ : Ctx m} {Γ : Ctx n}
                 (x : Var Δ A) (σ : Sub Γ Δ)
               → weaken {A' = A'} (x Ren./ σ) ≡ x Ren./ ++ₜ σ
weaken-ren-/ x σ = begin
  weaken (x Ren./ σ) ≡⟨ sym $ sub-p-wk (x Ren./ σ) ⟩
  (x Ren./ σ) [ p ]  ≡⟨ ren-/-assoc x σ p ⟩
  x Ren./ (σ ∘ p)    ≡⟨ cong (λ a → x Ren./ a) (∘-p-wk σ) ⟩
  x Ren./ ++ₜ σ ∎

++ₜ-∘r : ∀ {k m n A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
         (σ : Sub Δ Γ) (ρ : Ren E Δ)
         → ++ₜ {A = A} (σ ∘r ρ) ≡ σ ∘r ++ᵣ ρ
++ₜ-∘r <> _        = refl
++ₜ-∘r < σ , x > ρ = cong₂ <_,_> (++ₜ-∘r σ ρ) (weaken-/ x ρ)

++ᵣ-r∘ : ∀ {k m n A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
         (ρ : Ren Δ Γ) (σ : Sub E Δ)
         → ++ₜ {A = A} (ρ r∘ σ) ≡ ρ r∘ ++ₜ σ
++ᵣ-r∘ <>        σ = refl
++ᵣ-r∘ < ρ , x > σ = cong₂ <_,_> (++ᵣ-r∘ ρ σ) (weaken-ren-/ x σ)

↑-∘r-dist : ∀ {m n k A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
              (σ : Sub Δ Γ) (ρ : Ren E Δ)
            → ↑ {A = A} (σ ∘r ρ) ≡ ↑ σ ∘r Ren.↑ ρ
↑-∘r-dist σ ρ = begin
  ↑ (σ ∘r ρ)                         ≡⟨⟩
  < ++ₜ (σ ∘r ρ) , q >               ≡⟨ cong <_, q > (++ₜ-∘r σ ρ) ⟩ 
  < σ ∘r ++ᵣ ρ , q >                 ≡⟨ sym $ cong (<_, q >) (sub-comp++ σ (++ᵣ ρ) Ren.q) ⟩ 
  < ++ₜ σ ∘r < ++ᵣ ρ , Ren.q > , q > ≡⟨⟩
  ↑ σ ∘r Ren.↑ ρ
  ∎

var-wk : ∀ {n A A'} {Γ : Ctx n} (x : Var Γ A) → var (Ren.weaken {A' = A'} {Γ = Γ} x) ≡ weaken (var x)
var-wk (zero  , refl) = cong var (sym $ renP (zero , refl))
var-wk (suc i , refl) = sym $ begin
  var ((suc i , refl) Ren./ Ren.p) ≡⟨ cong var (renP (suc i , refl)) ⟩
  var (Ren.weaken (suc i , refl))  ≡⟨⟩
  var (suc (suc i) , refl)
  ∎

var-comp : ∀ {m n k A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
             (σ : Sub Δ Γ) (ρ : Ren E Δ) (x : Var Γ A)
           → var x [ σ ∘r ρ ] ≡ (var x [ σ ]) / ρ
var-comp < _ , _ >  _ (zero  , refl) = refl
var-comp < σ , x > ρ  (suc i , refl) = var-comp σ ρ (i , refl)

∘r-asso : ∀ {m n k A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
            (σ : Sub Δ Γ) (ρ : Ren E Δ) (t : Tm Γ A)
          → t [ σ ∘r ρ ] ≡ (t [ σ ]) / ρ
∘r-asso σ ρ (var x)   = var-comp σ ρ x
∘r-asso σ ρ (app f t) = cong₂ app (∘r-asso σ ρ f) (∘r-asso σ ρ t)
∘r-asso σ ρ (ƛ t)     = cong ƛ $ begin
  t [ ↑ (σ ∘r ρ) ]       ≡⟨ cong (t [_]) (↑-∘r-dist σ ρ) ⟩
  t [ ↑ σ ∘r Ren.↑ ρ ]   ≡⟨ ∘r-asso (↑ σ) (Ren.↑ ρ) t ⟩
  (t [ ↑ σ ]) / Ren.↑ ρ
  ∎

↑-r∘-dist : ∀ {m n k A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
              (ρ : Ren Δ Γ) (σ : Sub E Δ)
            → ↑ {A = A} (ρ r∘ σ) ≡ Ren.↑ ρ r∘ ↑ σ
↑-r∘-dist ρ σ = begin
  ↑ (ρ r∘ σ)           ≡⟨⟩
  < ++ₜ (ρ r∘ σ) , q > ≡⟨ cong <_, q > (++ᵣ-r∘ ρ σ) ⟩
  < ρ r∘ ++ₜ σ , q >   ≡⟨ sym $ cong <_, q > (sub-comp++r ρ (++ₜ σ) q) ⟩
  < ++ᵣ ρ r∘ ↑ σ , q > ≡⟨⟩
  Ren.↑ ρ r∘ ↑ σ
  ∎

r∘-asso : ∀ {m n k A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
            (ρ : Ren Δ Γ) (γ : Sub E Δ) (t : Tm Γ A)
          → t [ ρ r∘ γ ] ≡ (t / ρ) [ γ ]
r∘-asso <>        γ (var ())
r∘-asso < ρ , x > γ (var (zero  , refl)) = refl
r∘-asso < ρ , x > γ (var (suc i , refl)) = sym $ r∘-assoc (i , refl) ρ γ
r∘-asso ρ         γ (app f t)            = cong₂ app (r∘-asso ρ γ f) (r∘-asso ρ γ t)
r∘-asso ρ γ (ƛ t) = cong ƛ $ begin
  t [ ↑ (ρ r∘ γ) ]      ≡⟨ cong (t [_]) (↑-r∘-dist ρ γ) ⟩
  t [ Ren.↑ ρ r∘ ↑ γ ]  ≡⟨ r∘-asso (Ren.↑ ρ) (↑ γ) t ⟩
  (t / Ren.↑ ρ) [ ↑ γ ] ∎

++-∘r-p : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (σ : Sub Δ Γ)
          → ++ₜ {A = A} σ ≡ σ ∘r Ren.p
++-∘r-p <>        = refl
++-∘r-p < σ , x > = cong <_, _ > (++-∘r-p σ)

∘r-r∘ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (σ : Sub Δ Γ)
        → σ ∘r Ren.p {A = A} ≡ Ren.p r∘ (↑ σ)
∘r-r∘ σ = sym $ begin
  Ren.p r∘ < ++ₜ σ , q > ≡⟨ p-r∘-sub (++ₜ σ) q ⟩
  ++ₜ σ                  ≡⟨ ++-∘r-p σ ⟩
  σ ∘r Ren.p
  ∎

∘-∘r-asso-middle : ∀ {m n k j} {Θ : Ctx j} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
                     (σ₁ : Sub Δ Γ) (ρ : Ren E Δ) (σ₂ : Sub Θ E)
                   → (σ₁ ∘r ρ) ∘ σ₂ ≡ σ₁ ∘ (ρ r∘ σ₂)
∘-∘r-asso-middle <>         ρ σ₂ = refl
∘-∘r-asso-middle < σ₁ , x > ρ σ₂ = cong₂ <_,_> (∘-∘r-asso-middle σ₁ ρ σ₂) (sym $ r∘-asso ρ σ₂ x)
            
∘-∘r-asso : ∀ {m n k j} {Θ : Ctx j} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
              (σ₁ : Sub Δ Γ) (σ₂ : Sub E Δ) (ρ : Ren Θ E)
            → (σ₁ ∘ σ₂) ∘r ρ ≡ σ₁ ∘ (σ₂ ∘r ρ)
∘-∘r-asso <>         σ₂ _ = refl
∘-∘r-asso < σ₁ , x > σ₂ ρ = cong₂ <_,_> (∘-∘r-asso σ₁ σ₂ ρ) (sym $ ∘r-asso σ₂ ρ x)

lift-dist : ∀ {m n k} {A : Ty} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
              (γ₁ : Sub Δ Γ) (γ₂ : Sub E Δ)
            → ↑ {A = A} (γ₁ ∘ γ₂) ≡ ↑ γ₁ ∘ ↑ γ₂
lift-dist γ₁ γ₂ = begin
  ↑ (γ₁ ∘ γ₂)                 ≡⟨⟩
  < ++ₜ (γ₁ ∘ γ₂) , q >       ≡⟨ cong <_, q >  (++-∘r-p (γ₁ ∘ γ₂)) ⟩
  < (γ₁ ∘ γ₂) ∘r pᵣ , q >     ≡⟨ cong <_, q > (∘-∘r-asso γ₁ γ₂ Ren.p) ⟩
  < γ₁ ∘ (γ₂ ∘r pᵣ) , q >     ≡⟨ cong (<_, q > F.∘ (γ₁ ∘_)) (∘r-r∘ γ₂) ⟩
  < γ₁ ∘ (pᵣ r∘ ↑ γ₂) , q >   ≡⟨ cong <_, q > (sym $ ∘-∘r-asso-middle γ₁ Ren.p (↑ γ₂)) ⟩
  < (γ₁ ∘r pᵣ) ∘ ↑ γ₂ , q >   ≡⟨ cong (<_, q > F.∘ (_∘ ↑ γ₂)) (sym (++-∘r-p γ₁)) ⟩
  ↑ γ₁ ∘ ↑ γ₂
  ∎

-- Scwf law: substitution is associative -------------------------------------
subComp : ∀ {m n k} {A} {Γ : Ctx n} {Δ : Ctx m} {E : Ctx k}
            (t : Tm Γ A) (γ : Sub Δ Γ) (σ : Sub E Δ)
          → t [ γ ∘ σ ] ≡ t [ γ ] [ σ ]
subComp (var (zero  , refl)) < _ , _ > _ = refl
subComp (var (suc i , refl)) < γ , _ > σ = subComp (var (i , refl)) γ σ
subComp (app f t) γ σ = cong₂ app (subComp f γ σ) (subComp t γ σ)
subComp (ƛ t)     γ σ = cong ƛ $ begin
  t [ ↑ (γ ∘ σ) ]   ≡⟨ cong (t [_]) (lift-dist γ σ) ⟩
  t [ ↑ γ ∘ ↑ σ ]   ≡⟨ subComp t (↑ γ) (↑ σ) ⟩
  t [ ↑ γ ] [ ↑ σ ] ∎

-- Scfw law: composition is associative ----------------------------------------
compAssoc : ∀ {m n k j} {Θ : Ctx j} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
              (σ₁ : Sub Δ Γ) (σ₂ : Sub E Δ) (σ₃ : Sub Θ E)
            → σ₁ ∘ (σ₂ ∘ σ₃) ≡ (σ₁ ∘ σ₂) ∘ σ₃  
compAssoc <>          _ _  = refl
compAssoc < σ₁ , t > σ₂ σ₃ = cong₂ <_,_> (compAssoc σ₁ σ₂ σ₃) (subComp t σ₂ σ₃)


prop-β : ∀ {m n A B} {Δ : Ctx m} {Γ : Ctx n}
             (u : Tm (Γ ∙ B) A) (t : Tm Γ B) (σ : Sub Δ Γ)
         → u [ < id , t > ] [ σ ] ≡ u [ ↑ σ ] [ < id , (t [ σ ]) > ]
prop-β u t σ = begin
  u [ < id , t > ] [ σ ]                         ≡⟨ sym $ subComp u (< id , t >) σ ⟩
  u [ < id ∘ σ , t [ σ ] > ]                     ≡⟨ cong (λ z → u [ < z , t [ σ ] > ]) idL ⟩
  u [ < σ , t [ σ ] > ]                          ≡⟨ cong (λ z → u [ < z , t [ σ ] > ]) (sym idR) ⟩
  u [ < σ ∘ id , t [ σ ] > ]                     ≡⟨ cong (λ z → u [ < σ ∘ z , t [ σ ] > ]) (sym p-∘-sub) ⟩
  u [ < σ ∘ (p ∘ < id , t [ σ ] >) , t [ σ ] > ] ≡⟨ cong (λ z → u [ < z , t [ σ ] > ]) (compAssoc σ p _) ⟩
  u [ < (σ ∘ p) ∘ < id , t [ σ ] > , t [ σ ] > ] ≡⟨ cong (λ z → u [ < z ∘ < id , t [ σ ] > , t [ σ ] > ]) (∘-p-wk σ) ⟩
  u [ ↑ σ ∘ < id , t [ σ ] > ]                   ≡⟨ subComp u (↑ σ) _ ⟩ 
  u [ ↑ σ ] [ < id , (t [ σ ]) > ]
  ∎
  
prop-η : ∀ {m n A A'} {Δ : Ctx m} {Γ : Ctx n}
          (t : Tm Γ A) (σ : Sub Δ Γ)
        → weaken {A' = A'} (t [ σ ]) ≡ (weaken t) [ ↑ σ ]
prop-η t σ = begin
  weaken (t [ σ ])          ≡⟨ sym $ sub-p-wk (t [ σ ]) ⟩
  t [ σ ] [ p ]             ≡⟨ sym $ subComp t σ _ ⟩
  t [ σ ∘ p ]               ≡⟨ cong (t [_]) (sym $ p-∘-sub) ⟩
  t [ p ∘ < (σ ∘ p) , q > ] ≡⟨ subComp t p _ ⟩
  t [ p ] [ < σ ∘ p , q > ] ≡⟨ cong (λ z → (t [ p ]) [ < z , q > ]) (∘-p-wk σ) ⟩
  t [ p ] [ ↑ σ ]           ≡⟨ cong (_[ ↑ σ ]) (sub-p-wk t) ⟩
  weaken t [ ↑ σ ]
  ∎

infix 5 _~βη_
infix 5 _≈βη_

data _~βη_  {n} {Γ : Ctx n} : ∀ {A} (_ _ : Tm Γ A) → Set where

  varcong : ∀ {A} (x : Var Γ A) → var x ~βη var x

  apcong : ∀ {A B} {t t′ : Tm Γ (B ⇒ A)} {u u′ : Tm Γ B}
           → t ~βη t′
           → u ~βη u′
           → app t u ~βη app t′ u′

  ξ : ∀ {A B} {t u : Tm (Γ ∙ B) A} → t ~βη u → ƛ t ~βη ƛ u


  β : ∀ {A B} {t : Tm (Γ ∙ B) A} {u} → app (ƛ t) u ~βη t [ < id , u > ]
               
  η : ∀ {A B} {t : Tm Γ (A ⇒ B)} → ƛ (app (weaken t) q) ~βη t

  sym~βη : ∀ {A} {t₁ t₂ : Tm Γ A}
           → t₁ ~βη t₂
           → t₂ ~βη t₁
               
  trans~βη : ∀ {A} {t₁ t₂ t₃ : Tm Γ A}
             → t₁ ~βη t₂
             → t₂ ~βη t₃
             → t₁ ~βη t₃


data _≈βη_ {m} {Δ : Ctx m} : ∀ {n} {Γ : Ctx n} (_ _ : Sub Δ Γ) → Set where

  ⋄ : ∀ {σ σ' : Sub Δ ε} → σ ≈βη σ'

  ext : ∀ {n A} {Γ : Ctx n} {t t' : Tm Δ A} {σ σ' : Sub Δ Γ}
        → t ~βη t'
        → σ ≈βη σ'
        → < σ , t > ≈βη < σ' , t' >


refl~βη : ∀ {n A} {Γ : Ctx n} {t : Tm Γ A} → t ~βη t
refl~βη = trans~βη (sym~βη β) (β {t = q} )

refl≈βη : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ : Sub Δ Γ} → σ ≈βη σ
refl≈βη {σ = <>}        = ⋄
refl≈βη {σ = < σ , x >} = ext refl~βη refl≈βη

sym≈βη : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ σ' : Sub Δ Γ} → σ ≈βη σ' → σ' ≈βη σ
sym≈βη ⋄            = ⋄
sym≈βη (ext x σ~σ') = ext (sym~βη x) (sym≈βη σ~σ')

trans≈βη : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ₁ σ₂ σ₃ : Sub Δ Γ} → σ₁ ≈βη σ₂ → σ₂ ≈βη σ₃ → σ₁ ≈βη σ₃
trans≈βη ⋄              _            = ⋄
trans≈βη (ext x σ₁≈σ₂) (ext y σ₂≈σ₃) = ext (trans~βη x y) (trans≈βη σ₁≈σ₂ σ₂≈σ₃)


~βηequiv : ∀ {n A} {Γ : Ctx n} → IsEquivalence (_~βη_ {n} {Γ} {A})
~βηequiv = record { refl  = refl~βη
                  ; sym   = sym~βη
                  ; trans = trans~βη
                  }

Tm-βη-Setoid : ∀ {n A} {Γ : Ctx n} → Setoid _ _ 
Tm-βη-Setoid {n} {A} {Γ} =
  record { Carrier = Tm Γ A
         ; _≈_ = _~βη_ {n} {Γ} {A}
         ; isEquivalence = ~βηequiv
         }

≈βηequiv : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → IsEquivalence (_≈βη_ {m} {Δ} {n} {Γ})
≈βηequiv = record { refl  = refl≈βη
                  ; sym   = sym≈βη
                  ; trans = trans≈βη
                  }

Sub-βη-Setoid : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → Setoid _ _
Sub-βη-Setoid {m} {n} {Δ} {Γ} =
  record { Carrier = Sub Δ Γ
         ; _≈_ = _≈βη_
         ; isEquivalence = ≈βηequiv
         }

≡-to~βη : ∀ {n A} {Γ : Ctx n} {t u : Tm Γ A} → t ≡ u → t ~βη u
≡-to~βη refl = refl~βη

≡-to-≈βη : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ τ : Sub Δ Γ} → σ ≡ τ → σ ≈βη τ
≡-to-≈βη refl = refl≈βη

sub-p-wk~ : ∀ {n A A'} {Γ : Ctx n} (t : Tm Γ A) → t [ p {A = A'} ] ~βη weaken t
sub-p-wk~ t = ≡-to~βη (sub-p-wk t)

congSub-tm : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t t' : Tm Γ A} {σ : Sub Δ Γ}
             → t ~βη t' → t [ σ ] ~βη t' [ σ ]
congSub-tm (varcong x)           = refl~βη
congSub-tm (apcong t~t' t~t'')   = apcong (congSub-tm t~t') (congSub-tm t~t'')
congSub-tm (ξ t~t')              = ξ (congSub-tm t~t')
congSub-tm (sym~βη t~t')         = sym~βη (congSub-tm t~t')
congSub-tm (trans~βη t~t' t~t'') = trans~βη (congSub-tm t~t') (congSub-tm t~t'')
congSub-tm  {σ = σ} (β {t = t} {u})
  rewrite prop-β t u σ = β {t = t [ ↑ σ ]} {u = u [ σ ] }
congSub-tm {A = F ⇒ G} {σ = σ} (η {t = t})
  rewrite cong (ƛ F.∘ flip app q) (sym $ prop-η t σ) = η


cong-∘₁ : ∀ {m n k} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
            {σ σ' : Sub Δ Γ} {γ : Sub E Δ}
          → σ ≈βη σ'
          → σ ∘ γ ≈βη σ' ∘ γ
cong-∘₁ {σ = <>} {<>} ⋄              = refl≈βη
cong-∘₁ {γ = γ}      (ext t~t' σ≈σ') = ext (congSub-tm t~t') (cong-∘₁ σ≈σ') 

cong-↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {σ σ' : Sub Δ Γ} → σ ≈βη σ' → ↑ {A = A} σ ≈βη ↑ σ'
cong-↑ {A = A} {σ = σ} {σ'} σ≈σ'
  rewrite sym $ ∘-p-wk {A = A} σ
        | sym $ ∘-p-wk {A = A} σ' = ext refl~βη (cong-∘₁ σ≈σ')

congSub-s : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {t : Tm Γ A} {σ σ' : Sub Δ Γ}
            → σ ≈βη σ'
            → t [ σ ] ~βη t [ σ' ]
congSub-s {σ = <>} {<>}            ⋄            = refl~βη            
congSub-s {t = var (zero , refl)}  (ext x _)    = x
congSub-s {t = var (suc i , refl)} (ext _ σ≈σ') =  congSub-s {t = var (i , refl)} σ≈σ'
congSub-s {t = ƛ t}                (ext x σ≈σ') = ξ (congSub-s {t = t} (cong-↑ (ext x σ≈σ')))
congSub-s {t = app f t}            (ext x σ≈σ') = apcong (congSub-s {t = f} (ext x σ≈σ')) (congSub-s {t = t} (ext x σ≈σ'))

cong-sub~ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n}
             {t t' : Tm Γ A} {σ σ' : Sub Δ Γ}
           → t ~βη t'
           → σ ≈βη σ'
           → t [ σ ] ~βη t' [ σ' ]
cong-sub~ {t' = t'} t~t' σ≈σ' = trans~βη (congSub-tm t~t') (congSub-s {t = t'} σ≈σ')

cong-∘~ : ∀ {m n k} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
           {ρ σ : Sub Δ Γ} {ρ' σ' : Sub E Δ}
         → ρ ≈βη σ
         → ρ' ≈βη σ'
         → ρ ∘ ρ' ≈βη σ ∘ σ'
cong-∘~ ⋄           _             = ⋄
cong-∘~ (ext t ρ≈σ) ⋄             = ext (cong-sub~ t ⋄) (cong-∘~ ρ≈σ ⋄)
cong-∘~ (ext t ρ≈σ) (ext u ρ'≈σ') = ext (cong-sub~ t (ext u ρ'≈σ')) (cong-∘~ ρ≈σ (ext u ρ'≈σ'))

ImpSubScwf : Scwf
ImpSubScwf = record
               { Ty = Ty
               ; Ctx = Ctx
               ; Tm = Tm
               ; Sub = Sub
               ; ⋄ = ε
               ; _∙_ = _∙_
               ; _~_ = _~βη_
               ; _≈_ = _≈βη_
               ; IsEquiv~ = ~βηequiv
               ; IsEquiv≈ = ≈βηequiv
               ; id = id
               ; _∘_ = _∘_
               ; _[_] = _[_]
               ; <> = <>
               ; <_,_> = <_,_>
               ; p = p
               ; q = q
               ; id-zero = refl≈βη
               ; left-zero = refl≈βη
               ; idExt = refl≈βη
               ; idL = ≡-to-≈βη idL
               ; idR = ≡-to-≈βη idR
               ; assoc = λ γ δ ζ → (≡-to-≈βη F.∘ sym) (compAssoc γ δ ζ)
               ; subId = λ {n} {A} {Γ} {t} → ≡-to~βη (subId t)
               ; pCons = λ γ → ≡-to-≈βη $ p-∘-sub {γ = γ}
               ; qCons = refl~βη
               ; subComp = λ t {γ} {δ} → ≡-to~βη $ subComp t γ δ
               ; compExt = refl≈βη
               ; cong-sub = cong-sub~
               ; cong-<,> = ext
               ; cong-∘ = cong-∘~
               }

subLam : ∀ {n m A A'} {Δ : Ctx m} {Γ : Ctx n} {σ : Sub Δ Γ} {t : Tm (Γ ∙ A') A}
         → ƛ (t [ ↑ σ ]) ~βη ƛ (t [ < σ ∘ p , q > ])
subLam {A' = A'} {σ = σ} rewrite sym $ ∘-p-wk {A = A'} σ = refl~βη

η' : ∀ {n A B} {Γ : Ctx n} {t : Tm Γ (A ⇒ B)} → ƛ (app (t [ p ]) q) ~βη t
η' {A = A} {B} {t = t} rewrite sub-p-wk {A = A ⇒ B} {A' = A} t = η

ImpSubLamScwf : λβη-Scwf
ImpSubLamScwf = record
                  { scwf = ImpSubScwf
                  ; _`→_ = _⇒_
                  ; lam = ƛ
                  ; app = app
                  ; subApp = refl~βη
                  ; subLam = λ {n} {m} {A} {A'} {Δ} {Γ} {t} {σ} →
                           subLam {Δ = Δ} {Γ = Γ} {σ = σ} {t = t}
                  ; beta = β
                  ; eta = η'
                  ; cong-lam = ξ
                  ; cong-app = apcong
                  }
