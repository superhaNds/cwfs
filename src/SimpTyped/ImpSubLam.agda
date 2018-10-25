module ImpSubLam  where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec as Vec hiding ([_] ; map ; lookup)
open import Data.Fin hiding (lift)
open import Data.Product hiding (<_,_> ; map)
open import Relation.Binary.PropositionalEquality  hiding ([_])
open import Function using (_$_)
open ≡-Reasoning

infix 20 _/_
infix 20 _[_]

infix 8 _∘ᵣ_
infix 8 _∘_
infix 8 _∘r_
infix 8 _r∘_

data Ty : Set where
  o   : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Nat → Set
Ctx = Vec Ty

⋄ : Ctx 0
⋄ = []

_∙_ : ∀ {n} (Γ : Ctx n) (A : Ty) → Ctx (suc n)
Γ ∙ A = A ∷ Γ

Var : ∀ {n} (Γ : Ctx n) (A : Ty) → Set
Var Γ A = Σ (Fin _) (λ i → Vec.lookup i Γ ≡ A)

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

data Subst {m} (T : ∀ {k} → Ctx k → Ty → Set) (Δ : Ctx m) : ∀ {n} (Γ : Ctx n) → Set where
  <> : Subst T Δ ⋄
  
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

module Ren where

  q : ∀ {n A} {Γ : Ctx n} → Var (Γ ∙ A) A
  q = (zero , refl)

  weaken : ∀ {A A' m} {Γ : Ctx m}
           → Var Γ A
           → Var (Γ ∙ A') A
  weaken (i , refl) = (suc i , refl)

  infixl 20 _/_

  _/_ : ∀ {m n} {A : Ty} {Δ : Ctx m} {Γ : Ctx n} {T : ∀ {k} → Ctx k → Ty → Set}
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

mutual

  renId : ∀ {n A} {Γ : Ctx n} (x : Var Γ A) → x Ren./ Ren.id ≡ x
  renId {Γ = []}    (()    , _)
  renId {Γ = _ ∷ _} (zero  , refl) = refl
  renId {Γ = _ ∷ _} (suc i , refl) = renP (i , refl)

  renP : ∀ {n A B} {Γ : Ctx n} (x : Var Γ A) → x Ren./ Ren.p {A = B} ≡ Ren.weaken x
  renP x = trans (wk-ren-eq Ren.id x) (cong Ren.weaken (renId x))

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
              → (++ ρ' VarTemp) ∘ᵣ < ρ , x > ≡ ρ' ∘ᵣ ρ
ren-comp-++ {ρ' = <>}         {ρ} = refl
ren-comp-++ {ρ' = < ρ' , x >} {ρ} = cong₂ <_,_> ren-comp-++ (wk-ext-ren {ρ = ρ})

renIdR : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ρ ∘ᵣ Ren.id ≡ ρ
renIdR <>        = refl
renIdR < ρ , x > = cong₂ <_,_> (renIdR ρ) (renId x)

renExtId : ∀ {n A} {Γ : Ctx n} → Ren.id {Γ = Γ ∙ A} ≡ < Ren.p , Ren.q  >
renExtId = refl

ren-qSub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {ρ : Ren Δ Γ} {x : Var Δ A} → Ren.q Ren./ < ρ , x > ≡ x
ren-qSub = refl

mutual 

  renPcomp : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {ρ : Ren Δ Γ} {x : Var Δ A} → Ren.p ∘ᵣ < ρ , x > ≡ ρ
  renPcomp = trans ren-comp-++ (renIdL _)

  renIdL : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → Ren.id ∘ᵣ ρ ≡ ρ
  renIdL <>        = refl
  renIdL < ρ , x > = cong₂ <_,_> renPcomp refl

ren-assoc : ∀ {k m n A} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
              {ρ : Ren Γ E} {ρ' : Ren Δ Γ} {x : Var E A} → x Ren./ ρ Ren./ ρ' ≡ x Ren./ (ρ ∘ᵣ ρ')
ren-assoc {ρ = <>}        {_}  {()    , _}
ren-assoc {ρ = < ρ , x >} {_}  {zero  , refl} = refl
ren-assoc {ρ = < ρ , x >} {ρ'} {suc i , refl} = ren-assoc {ρ = ρ} {x = (i , refl) }

∘ᵣ-assoc : ∀ {j k m n} {Ζ : Ctx j} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
             {ρ₁ : Ren E Ζ } {ρ₂ : Ren Γ E } {ρ₃ : Ren Δ Γ }
           → ρ₁ ∘ᵣ (ρ₂ ∘ᵣ ρ₃) ≡ (ρ₁ ∘ᵣ ρ₂) ∘ᵣ ρ₃
∘ᵣ-assoc {ρ₁ = <>}                   = refl
∘ᵣ-assoc {ρ₁ = < ρ₁ , x >} {ρ₂} {ρ₃} = cong₂ <_,_> (∘ᵣ-assoc {ρ₁ = ρ₁} {ρ₂}) (sym $ ren-assoc {ρ = ρ₂} {x = x})

substWeakRen : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ++ {A = A} (renToSub ρ) TmTemp ≡ renToSub (++ ρ VarTemp)
substWeakRen <>        = refl
substWeakRen < ρ , x > = cong₂ <_,_> (substWeakRen ρ) (cong var (renP x))

↑id-id : ∀ {n A} {Γ : Ctx n} → ↑ {A = A} {Γ} id ≡ id
↑id-id = cong₂ <_,_> (substWeakRen Ren.id) refl

subRen : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (t : Tm Γ A) (ρ : Ren Δ Γ) → t [ renToSub ρ ] ≡ t / ρ
subRen (var (()    , _))    <>
subRen (var (zero  , refl)) < ρ , _ > = refl
subRen (var (suc i , refl)) < ρ , _ > = subRen (var (i , refl)) ρ
subRen (ƛ t) ρ =
  cong ƛ (trans (cong-sub {t₁ = t} refl
                (cong₂ <_,_> (substWeakRen ρ) refl))
        (subRen t (lift ρ VarTemp)))
subRen (app f t) ρ = cong₂ app (subRen f ρ) (subRen t ρ)

renTmId : ∀ {n A} {Γ : Ctx n} (t : Tm Γ A) → t / Ren.id ≡ t
renTmId (var x)   = cong var (renId x)
renTmId (ƛ t)     = cong ƛ (renTmId t)
renTmId (app f t) = cong₂ app (renTmId f) (renTmId t)

subId : ∀ {n A} {Γ : Ctx n} (t : Tm Γ A) → t [ id ] ≡ t
subId t = trans (subRen t Ren.id) (renTmId t)
  
sub-p-wk : ∀ {n A A'} {Γ : Ctx n} (t : Tm Γ A) → t [ p {A = A'} ] ≡ weaken t
sub-p-wk t = trans (subRen t Ren.p) refl

++ₜ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} → Sub Δ Γ → Sub (Δ ∙ A) Γ
++ₜ γ = ++ γ TmTemp

∘-p-wk : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub Δ Γ) → γ ∘ p {A = A} ≡ ++ₜ γ
∘-p-wk <>        = refl
∘-p-wk < γ , t > = cong₂ <_,_> (∘-p-wk γ) (sub-p-wk t)

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

auxlemm₂ : ∀ {k m n A B} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) (γ : Sub E Δ) (t : Tm E B)
           → (++ᵣ {A = A} ρ) r∘ (↑ γ) ≡ (++ᵣ (++ᵣ ρ) r∘ < < ++ₜ γ , weaken t > , q >)
auxlemm₂ <>        _ _ = refl
auxlemm₂ < ρ , x > γ t = cong₂ <_,_> (auxlemm₂ ρ γ t) (sym $ begin
  Ren.weaken (Ren.weaken x) Ren./ < < ++ₜ γ , weaken t > , q > ≡⟨ wk-ext-ren' {γ = < ++ₜ γ , weaken t >} {Ren.weaken x} ⟩
  Ren.weaken x Ren./ < ++ₜ γ , weaken t >                      ≡⟨ wk-ext-ren' {γ = ++ₜ γ} ⟩
  x Ren./ ++ₜ γ                                                ≡⟨ sym $ wk-ext-ren' {γ = ++ₜ γ} ⟩
  Ren.weaken x Ren./ ↑ γ
  ∎)

idR : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → γ ∘ id ≡ γ
idR {γ = <>}        = refl
idR {γ = < γ , t >} = cong₂ <_,_> idR (subId t)

wk-∘-↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ++ᵣ {A = A} ρ ≡ Ren.p ∘ᵣ Ren.↑ ρ
wk-∘-↑ <>        = refl
wk-∘-↑ < ρ , x > = cong (<_, Ren.weaken x >) (trans (wk-∘-↑ ρ) (auxlemm₁ Ren.id ρ x))

∘ᵣ-p-wk : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ρ ∘ᵣ Ren.p {A = A} ≡ ++ᵣ ρ
∘ᵣ-p-wk <> = refl
∘ᵣ-p-wk < ρ , x > = cong₂ <_,_> (∘ᵣ-p-wk ρ) (renP x)

p-↑ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ρ ∘ᵣ Ren.p {A = A} ≡ Ren.p ∘ᵣ Ren.↑ ρ
p-↑ ρ = trans (∘ᵣ-p-wk ρ) (wk-∘-↑ ρ)

wk-sub-eq : ∀ {m n A A'} {Δ : Ctx m} {Γ : Ctx n}
              {u : Tm Δ A} (γ : Sub Δ Γ) (t : Tm Γ A') → weaken t [ < γ , u > ] ≡ t [ γ ]
wk-sub-eq γ t = {!!}

wk-var : ∀ {n A B} {Γ : Ctx n} {x : Var Γ A} → var (Ren.weaken {A' = B} x) ≡ weaken (var x)
wk-var {A = A} {B} {x = x} rewrite renP {B = B} x = refl

++-renSub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → renToSub (++ᵣ {A = A} ρ) ≡ ++ₜ (renToSub ρ)
++-renSub <> = refl
++-renSub < ρ , x > = cong₂ <_,_> (++-renSub ρ) wk-var

sub-∘-++ : ∀ {k m n A} {Δ : Ctx m} {Γ : Ctx n} {E : Ctx k}
             {γ' : Sub Γ E} {γ} {t : Tm Δ A} → ++ₜ γ' ∘ < γ , t > ≡ γ' ∘ γ
sub-∘-++ {γ' = <>}         = refl
sub-∘-++ {γ' = < γ' , u >} {γ} {t} = cong₂ <_,_> sub-∘-++ (wk-sub-eq γ u )

mutual

  p-∘-sub : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} {t : Tm Δ A} → p ∘ < γ , t > ≡ γ
  p-∘-sub {A = A} {Γ = Γ} {γ} {t}
    rewrite ++-renSub {A = A} (Ren.id {Γ = Γ}) = trans (sub-∘-++ {γ' = id} {γ} {t}) idL 

  idL : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → id ∘ γ ≡ γ
  idL {γ = <>}        = refl
  idL {γ = < γ , t >} = cong <_, t > p-∘-sub
