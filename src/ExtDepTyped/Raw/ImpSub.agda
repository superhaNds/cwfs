module ExtDepTyped.Raw.ImpSub where

open import Data.Nat renaming (ℕ to Nat) using (_+_ ; suc ; zero)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_] ; lookup)
open import Data.Vec.Properties hiding (map-lookup-allFin)
open import Function hiding (id ; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_] ; cong-∘)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary using (Setoid ; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as EqR
open import Unityped.Ucwf
open ≡-Reasoning
open import Unityped.ImpSub as Ren using (Ren ; _∙_ ; lookup ; map-lookup-allFin)

data Tm (n : Nat) : Set where
  var : (i : Fin n)       → Tm n   -- variables as de Bruijn indices
  app : Tm n → Tm n       → Tm n   -- application
  ƛ   : Tm (suc n)        → Tm n   -- λ abstraction \Gl-
  Π   : Tm n → Tm (suc n) → Tm n   -- Π type
  U   :                     Tm n   -- universe

q : ∀ {n} → Tm (suc n)
q = var zero

infixl 9 _/_

-- Renaming operation

_/_ : ∀ {m n} → Tm n → Ren m n → Tm m
var i   / ρ = var (lookup i ρ)
app f t / ρ = app (f / ρ) (t / ρ)
ƛ t     / ρ = ƛ (t / Ren.↑ ρ)
Π A B   / ρ = Π (A / ρ) (B / Ren.↑ ρ)
U       / _ = U

-- Substitutions as vectors of terms

Sub : Nat → Nat → Set
Sub m n = Vec (Tm m) n

infix 10 _,_

-- Cons synonym

_,_ : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)
σ , t = t ∷ σ

-- weakening a term is renaming it in the projection renaming

weaken : ∀ {n} → Tm n → Tm (suc n)
weaken t = t / Ren.p

-- weakening and extending a substitution (lifting)

↑ : ∀ {m n} → Sub m n → Sub (1 + m) (1 + n)
↑ σ = map weaken σ , q

-- identity substitution

id : ∀ {n} → Sub n n
id = map var Ren.id

-- projection substitution

p : ∀ {n} → Sub (suc n) n
p = map var Ren.p

-- substitution as a meta-level operation

_[_] : ∀ {m n} → Tm n → Sub m n → Tm m
var i   [ σ ] = lookup i σ
app f t [ σ ] = app (f [ σ ]) (t [ σ ])
ƛ t     [ σ ] = ƛ (t [ ↑ σ ])
Π A B   [ σ ] = Π (A [ σ ]) (B [ ↑ σ ])
U       [ _ ] = U

infix 12 _∘_

-- Substitution composition

_∘_ : ∀ {k m n} → Sub m n → Sub k m → Sub k n
σ₁ ∘ σ₂ = map (_[ σ₂ ]) σ₁

-- Composing renamings and substitutions

_r∘_ : ∀ {m n k} → Ren m n → Sub k m → Sub k n
ρ r∘ σ = map (flip lookup σ) ρ

_∘r_ : ∀ {m n k} → Sub m n → Ren k m → Sub k n
σ ∘r ρ = map (λ t → t / ρ) σ

-- lookup in p returns the successor of the index

lookup-p : ∀ {n} (i : Fin n) → lookup i p ≡ var (suc i)
lookup-p i = begin
  lookup i (map var (map suc Ren.id)) ≡⟨ Ren.lookup-map i var _ ⟩
  var (lookup i (map suc Ren.id))     ≡⟨ cong var (Ren.lookup-p i) ⟩
  var (suc i)
  ∎

-- weakening a variable increases the index

weaken-var : ∀ {n} (i : Fin n) → weaken (var i) ≡ var (suc i)
weaken-var i = cong var (Ren.lookup-p i)

var-refl : ∀ {n} {i : Fin n} → i ≡ i → var i ≡ var i
var-refl refl = refl

lam-refl : ∀ {n} {t : Tm (suc n)} → t ≡ t → ƛ t ≡ ƛ t
lam-refl refl = refl

app-refl : ∀ {n} {t t' u u' : Tm n} → t ≡ t' → u ≡ u' → app t u ≡ app t' u'
app-refl refl refl = refl

-- weakening a renaming wrapped in vars is weakening the renaming and wrapping them in var

map-var-weaken : ∀ {n m} (ρ : Ren m n) → map weaken (map var ρ) ≡ map var (map suc ρ)
map-var-weaken [] = refl
map-var-weaken (i ∷ ρ) =
  trans (cong (map weaken (map var ρ) ,_) (weaken-var i))
        (cong (_, var (suc i)) (map-var-weaken ρ))

-- extended identity is p with the zeroth variable

idExt : ∀ {n} → id {1 + n} ≡ (p , q)
idExt = refl

-- lifting id is the extended id

↑-id : ∀ {n} → ↑ id ≡ id {1 + n}
↑-id = cong (_, q) (map-var-weaken Ren.id)

-- lookup in id returns the variable with index as the input

lookup-id : ∀ {n} (i : Fin n) → lookup i id ≡ var i
lookup-id zero    = refl
lookup-id (suc i) = begin
  lookup i (map var Ren.p) ≡⟨ Ren.lookup-map i var Ren.p ⟩
  var (lookup i Ren.p)     ≡⟨ cong var (Ren.lookup-p i) ⟩
  var (suc i)
  ∎

-- id vanishes in substitution

subId : ∀ {n} {t : Tm n} → t [ id ] ≡ t
subId {t = U}       = refl
subId {t = var i}   = lookup-id i
subId {t = app t f} = cong₂ app subId subId
subId {t = ƛ t}     = cong ƛ $ begin
  t [ ↑ id ] ≡⟨ cong (t [_]) ↑-id ⟩
  t [ id ]   ≡⟨ subId ⟩
  t
  ∎
subId {t = Π A B} = begin
  Π (A [ id ]) (B [ ↑ id ]) ≡⟨ cong (λ x → Π x _) subId ⟩
  Π A (B [ ↑ id ])          ≡⟨ cong (λ x → Π A (B [ x ])) ↑-id ⟩
  Π A (B [ id ])            ≡⟨ cong (Π A) subId ⟩
  Π A B
  ∎

-- renaming is associative

/-asso : ∀ {m n k} (ρ : Ren m n) (τ : Ren k m) t → t / (ρ ∙ τ) ≡ (t / ρ) / τ
/-asso ρ τ U         = refl
/-asso ρ τ (var i)   = cong var (Ren.lookup-map i _ ρ)
/-asso ρ τ (app f t) = cong₂ app (/-asso ρ τ f) (/-asso ρ τ t)
/-asso ρ τ (ƛ t)     = cong ƛ $ begin
  t / Ren.↑ (ρ ∙ τ)       ≡⟨ cong (t /_) (Ren.↑-dist ρ τ) ⟩
  t / (Ren.↑ ρ ∙ Ren.↑ τ) ≡⟨ /-asso (Ren.↑ ρ) (Ren.↑ τ) t ⟩
  t / Ren.↑ ρ / Ren.↑ τ
  ∎
/-asso ρ τ (Π A B) = begin
  Π (A / ρ ∙ τ) (B / Ren.↑ (ρ ∙ τ))       ≡⟨ cong (λ x → Π x _) (/-asso ρ τ A) ⟩
  Π (A / ρ / τ) (B / Ren.↑ (ρ ∙ τ))       ≡⟨ cong (λ x → Π ((A / ρ) / τ) (B / x) ) (Ren.↑-dist ρ τ) ⟩
  Π (A / ρ / τ) (B / (Ren.↑ ρ ∙ Ren.↑ τ)) ≡⟨ cong (Π ((A / ρ) / τ)) (/-asso (Ren.↑ ρ) (Ren.↑ τ) B) ⟩
  Π (A / ρ / τ) (B / Ren.↑ ρ / Ren.↑ τ)
  ∎

-- Properties relating renamings and substitutions
  
↑-map-var : ∀ {m n} (ρ : Ren m n) → ↑ (map var ρ) ≡ map var (Ren.↑ ρ)
↑-map-var []      = refl
↑-map-var (i ∷ ρ) =
  trans (cong (λ x → q ∷ weaken (var i) ∷ x) (map-var-weaken ρ))
        (cong (λ x → q ∷ x ∷ map var (map suc ρ)) (weaken-var i))

/-map-var : ∀ {m n} (ρ : Ren m n) (t : Tm n) → t / ρ ≡ t [ map var ρ ]
/-map-var _       U             = refl
/-map-var []      (var ())
/-map-var (_ ∷ _) (var zero)    = refl
/-map-var (_ ∷ ρ) (var (suc i)) = /-map-var ρ (var i)
/-map-var ρ (app f t)           = cong₂ app (/-map-var ρ f) (/-map-var ρ t)
/-map-var ρ (ƛ t)
  rewrite ↑-map-var ρ           = cong ƛ (/-map-var (Ren.↑ ρ) t)
/-map-var ρ (Π A B)
  rewrite ↑-map-var ρ           = cong₂ Π (/-map-var ρ A) (/-map-var (Ren.↑ ρ) B)

↑-map-p : ∀ {n} → map var (Ren.↑ Ren.p) ≡ ↑ (p {n})
↑-map-p = sym $ ↑-map-var Ren.p

/-↑-[] : ∀ {n} {t : Tm (suc n)} → t / (Ren.↑ Ren.p) ≡ t [ ↑ p ]
/-↑-[] {t = t} = begin
  t / (Ren.↑ Ren.p)           ≡⟨ /-map-var _ t ⟩
  t [ map var (Ren.↑ Ren.p) ] ≡⟨ cong (t [_]) ↑-map-p ⟩
  t [ ↑ p ]
  ∎

p-∘-lookup : ∀ {m n} (σ : Sub m (1 + n)) → p {n} ∘ σ ≡ map (flip lookup σ) Ren.p
p-∘-lookup σ = begin
  map (_[ σ ]) (map var (Ren.p)) ≡⟨ sym $ map-∘ (_[ σ ]) var Ren.p  ⟩
  map (λ i → var i [ σ ]) Ren.p  ≡⟨⟩
  map (flip lookup σ) Ren.p
  ∎

map-lookup-p : ∀ {n m} (σ : Sub m (1 + n)) → map (flip lookup σ) Ren.p ≡ tail σ
map-lookup-p (t ∷ σ) = begin
  map (flip lookup (σ , t)) Ren.p   ≡⟨ sym $ map-∘ (flip lookup (σ , t)) suc Ren.id ⟩
  map (flip lookup σ) Ren.id        ≡⟨ cong (map (λ i → lookup i σ)) Ren.id-allFin ⟩
  map (flip lookup σ) (allFin _)    ≡⟨ map-lookup-allFin σ ⟩
  σ
  ∎

-- p on the left of composition drops the last term

p-∘ : ∀ {m n} {t : Tm n} {σ : Sub n m} → p ∘ (σ , t) ≡ σ
p-∘ {t = t} {σ} = trans (p-∘-lookup (σ , t)) (map-lookup-p (σ , t))

-- weakening a term is the same as substituting with p

wk-sub-p : ∀ {n} {t : Tm n} → weaken t ≡ t [ p ]
wk-sub-p {t = U}       = refl
wk-sub-p {t = var i}   = trans (weaken-var i) (sym $ lookup-p i)
wk-sub-p {t = app f t} = cong₂ app wk-sub-p wk-sub-p
wk-sub-p {t = ƛ t}     = cong ƛ /-↑-[]
wk-sub-p {t = Π A B}   = cong₂ Π wk-sub-p /-↑-[]

-- hence, composing with p is weakening a substitution

map-wk-p : ∀ {m n} {σ : Sub m n} → σ ∘ p ≡ map weaken σ
map-wk-p {σ = []}    = refl
map-wk-p {σ = t ∷ σ} =
  trans (cong (λ x → _ , x) (sym $ wk-sub-p))
        (cong (_, weaken t) map-wk-p)

-- misc properties

/-p : ∀ {m n} (ρ : Ren m n) (t : Tm n) → (t / ρ) / Ren.p ≡ (t / Ren.p) / (Ren.↑ ρ)
/-p ρ t =
  trans (sym (/-asso ρ _ t))
        (sym $ trans (sym (/-asso Ren.p (Ren.↑ ρ) t))
                     (cong (t /_) (sym Ren.∙-p)))

↑-∘r-dist : ∀ {m n k} (σ : Sub m n) (ρ : Ren k m) → ↑ (σ ∘r ρ) ≡ ↑ σ ∘r Ren.↑ ρ
↑-∘r-dist σ ρ = begin
  ↑ (σ ∘r ρ)                                   ≡⟨⟩
  map weaken (σ ∘r ρ) , q                      ≡⟨ cong (_, q) (sym $ map-∘ _ _ σ) ⟩
  map (λ t → t / ρ / Ren.p) σ , q              ≡⟨ cong (_, q) (map-cong (/-p ρ) σ) ⟩
  map (λ t → t / Ren.p / Ren.↑ ρ) σ , q        ≡⟨ cong (_, q) (map-∘ _ _ σ) ⟩
  map (flip _/_ (Ren.↑ ρ)) (map weaken σ) , q  ≡⟨⟩
  ↑ σ ∘r Ren.↑ ρ
  ∎

↑-r∘-dist : ∀ {m n k} (ρ : Ren m n) (σ : Sub k m) → ↑ (ρ r∘ σ) ≡ Ren.↑ ρ r∘ ↑ σ
↑-r∘-dist ρ σ = cong (_, q) (trans (sym (map-∘ _ _ ρ))
                     (sym $ trans (sym (map-∘ (flip lookup (↑ σ)) suc ρ))
                                  (map-cong (λ i → Ren.lookup-map i weaken σ) ρ) ))

∘r-asso : ∀ {m n k} (σ : Sub m n) (ρ : Ren k m) (t : Tm n) → t [ σ ∘r ρ ] ≡ (t [ σ ]) / ρ
∘r-asso _ _ U         = refl
∘r-asso σ ρ (var i)   = Ren.lookup-map i (_/ ρ) σ
∘r-asso σ ρ (app f t) = cong₂ app (∘r-asso σ ρ f) (∘r-asso σ ρ t)
∘r-asso σ ρ (ƛ t)     = cong ƛ $ begin
  t [ ↑ (σ ∘r ρ) ]       ≡⟨ cong (t [_]) (↑-∘r-dist _ _) ⟩
  t [ ↑ σ ∘r Ren.↑ ρ ]   ≡⟨ ∘r-asso (↑ σ) (Ren.↑ ρ) t ⟩
  (t [ ↑ σ ]) / Ren.↑ ρ
  ∎
∘r-asso σ ρ (Π A B) = begin
  Π (A [ σ ∘r ρ ]) (B [ ↑ (σ ∘r ρ) ])    ≡⟨ cong (λ x → Π x _) (∘r-asso σ ρ A) ⟩
  Π (A [ σ ] / ρ) (B [ ↑ (σ ∘r ρ) ])     ≡⟨ cong (λ x → Π (A [ σ ] / ρ) (B [ x ])) (↑-∘r-dist _ _) ⟩
  Π (A [ σ ] / ρ) (B [ ↑ σ ∘r Ren.↑ ρ ]) ≡⟨ cong (Π (A [ σ ] / ρ)) (∘r-asso (↑ σ) (Ren.↑ ρ) B) ⟩ 
  Π (A [ σ ] / ρ) (B [ ↑ σ ] / Ren.↑ ρ) 
  ∎

r∘-asso : ∀ {m n k} (ρ : Ren m n) (σ : Sub k m) t → t [ ρ r∘ σ ] ≡ (t / ρ) [ σ ]
r∘-asso _ _ U         = refl
r∘-asso ρ σ (var i)   = Ren.lookup-map i (flip lookup σ) ρ
r∘-asso ρ σ (app f t) = cong₂ app (r∘-asso ρ σ f) (r∘-asso ρ σ t)
r∘-asso ρ σ (ƛ t)     = cong ƛ $ begin
  t [ ↑ (ρ r∘ σ) ]      ≡⟨ cong (t [_]) (↑-r∘-dist ρ σ) ⟩
  t [ Ren.↑ ρ r∘ ↑ σ ]  ≡⟨ r∘-asso (Ren.↑ ρ) (↑ σ) t ⟩
  (t / Ren.↑ ρ) [ ↑ σ ]
  ∎
r∘-asso ρ σ (Π A B) = begin
  Π (A [ ρ r∘ σ ]) (B [ ↑ (ρ r∘ σ) ])       ≡⟨ cong (λ x → Π x _) (r∘-asso ρ σ A) ⟩
  Π ((A / ρ) [ σ ]) (B [ ↑ (ρ r∘ σ) ])      ≡⟨ cong (λ x → Π ((A / ρ) [ σ ]) (B [ x ])) (↑-r∘-dist _ _) ⟩
  Π ((A / ρ) [ σ ]) (B [ Ren.↑ ρ r∘ ↑ σ ])  ≡⟨ cong (Π ((A / ρ) [ σ ])) (r∘-asso (Ren.↑ ρ) (↑ σ) B) ⟩
  Π ((A / ρ) [ σ ]) ((B / Ren.↑ ρ) [ ↑ σ ])
  ∎

∘r-r∘ : ∀ {m n} {σ : Sub m n} → σ ∘r Ren.p ≡ Ren.p r∘ (↑ σ)
∘r-r∘ =
  sym $ trans (sym (map-∘ _ _ Ren.id))
              (trans (cong (map (λ i → lookup (suc i) (↑ _))) Ren.id-allFin)
                     (map-lookup-allFin _))

-- lifting distributes over composition

↑-dist : ∀ {m n k} (σ₁ : Sub m n) (σ₂ : Sub k m) → ↑ (σ₁ ∘ σ₂) ≡ ↑ σ₁ ∘ ↑ σ₂
↑-dist σ₁ σ₂ = begin
  ↑ (σ₁ ∘ σ₂)                              ≡⟨⟩
  map weaken (map (_[ σ₂ ]) σ₁) , q        ≡⟨ cong (_, q) (sym $ map-∘ weaken (_[ σ₂ ]) σ₁) ⟩
  map (λ t → t [ σ₂ ] / Ren.p) σ₁ , q      ≡⟨ cong (_, q) (map-cong (λ t → sym (∘r-asso _ _ t)) σ₁) ⟩
  map (_[ σ₂ ∘r Ren.p ]) σ₁ , q            ≡⟨ cong (_, q) (map-cong (λ x → cong (x [_]) ∘r-r∘) σ₁) ⟩
  map (_[ Ren.p r∘ (↑ σ₂) ]) σ₁ , q        ≡⟨ cong (_, q) (map-cong (r∘-asso _ _) σ₁) ⟩
  map (λ t → (t / Ren.p) [ ↑ σ₂ ]) σ₁ , q  ≡⟨ cong (_, q) (map-∘ _ _ σ₁) ⟩
  map (_[ ↑ σ₂ ]) (↑ σ₁)                   ≡⟨⟩
  ↑ σ₁ ∘ ↑ σ₂
  ∎

-- substitution is associative

subComp : ∀ {m n k} t {σ : Sub m n} {τ : Sub k m} → t [ σ ∘ τ ] ≡ t [ σ ] [ τ ]
subComp U                     = refl
subComp (var zero)    {_ ∷ _} = refl
subComp (var (suc i)) {_ ∷ _} = subComp (var i)
subComp (app f t)     {_}     = cong₂ app (subComp f) (subComp t)
subComp (ƛ t)         {σ} {τ} = cong ƛ $ begin
  t [ ↑ (σ ∘ τ) ]   ≡⟨ cong (t [_]) (↑-dist σ τ) ⟩
  t [ ↑ σ ∘ ↑ τ ]   ≡⟨ subComp t ⟩
  t [ ↑ σ ] [ ↑ τ ]
  ∎
subComp (Π A B) {σ} {τ} = begin
  Π (A [ σ ∘ τ ]) (B [ ↑ (σ ∘ τ) ])     ≡⟨ cong (λ x → Π x _) (subComp A) ⟩
  Π (A [ σ ] [ τ ]) (B [ ↑ (σ ∘ τ) ])   ≡⟨ cong (λ x → Π (A [ σ ] [ τ ]) (B [ x ])) (↑-dist σ τ) ⟩
  Π (A [ σ ] [ τ ]) (B [ ↑ σ ∘ ↑ τ ])   ≡⟨ cong (Π (A [ σ ] [ τ ])) (subComp B) ⟩
  Π (A [ σ ] [ τ ]) (B [ ↑ σ ] [ ↑ τ ]) 
  ∎

-- composition is associative

∘-asso : ∀ {m n k j} {σ₁ : Sub m n} {σ₂ : Sub k m} {σ₃ : Sub j k}
         → (σ₁ ∘ σ₂) ∘ σ₃ ≡ σ₁ ∘ (σ₂ ∘ σ₃)
∘-asso {σ₁ = []}     {_} {_}   = refl
∘-asso {σ₁ = t ∷ σ₁} {σ₂} {σ₃} = begin
  (σ₁ ∘ σ₂) ∘ σ₃ , t [ σ₂ ] [ σ₃ ]  ≡⟨ cong (_, t [ σ₂ ] [ σ₃ ]) ∘-asso ⟩
  σ₁ ∘ (σ₂ ∘ σ₃) , t [ σ₂ ] [ σ₃ ]  ≡⟨ cong (σ₁ ∘ (σ₂ ∘ σ₃) ,_) (sym $ subComp t) ⟩
  σ₁ ∘ (σ₂ ∘ σ₃) , t [ σ₂ ∘ σ₃ ]
  ∎

-- id is a left identity in composition

idL : ∀ {m n} {σ : Sub m n} → id ∘ σ ≡ σ
idL {σ = []}    = refl
idL {σ = t ∷ σ} = cong (_, t) p-∘

-- id is a right identity in composition

idR : ∀ {m n} {σ : Sub m n} → σ ∘ id ≡ σ
idR {σ = []} = refl
idR {σ = t ∷ σ}
  rewrite subId {t = t}
        | idR {σ = σ} = refl

prop-β : ∀ {m n} {σ : Sub m n} {t B}
         → B [ id , t ] [ σ ] ≡ B [ ↑ σ ] [ id , (t [ σ ]) ]
prop-β {σ = σ} {t} {B} = sym $ begin
  B [ ↑ σ ] [ id , (t [ σ ]) ]               ≡⟨ sym $ subComp B ⟩
  B [ ↑ σ ∘ (id , t [ σ ]) ]                 ≡⟨ cong (λ x → B [ (x , q) ∘ (id , t [ σ ]) ]) (sym $ map-wk-p) ⟩
  B [ (σ ∘ p , q) ∘ (id , t [ σ ]) ]         ≡⟨⟩
  B [ (σ ∘ p) ∘ (id , t [ σ ]) , t [ σ ] ]   ≡⟨ cong (λ x → B [ x , t [ σ ] ]) ∘-asso ⟩
  B [ σ ∘ (p ∘ (id , t [ σ ])) , t [ σ ] ]   ≡⟨ cong (λ x → B [ σ ∘ x , t [ σ ] ]) p-∘ ⟩
  B [ σ ∘ id , t [ σ ] ]                     ≡⟨ cong (λ x → B [ x , t [ σ ] ]) idR ⟩
  B [ σ , t [ σ ] ]                          ≡⟨ cong (λ x → B [ x , t [ σ ] ]) (sym idL) ⟩
  B [ id ∘ σ , t [ σ ] ]                     ≡⟨⟩
  B [ (id , t) ∘ σ ]                         ≡⟨ subComp B ⟩ 
  B [ id , t ] [ σ ]
  ∎

-- weakening a substitution is substituting a weakened term with the lifted substitution

prop-η : ∀ {n m} t (σ : Sub m n) → weaken (t [ σ ]) ≡ (weaken t) [ ↑ σ ]
prop-η t σ = sym $ begin
  weaken t [ ↑ σ ]        ≡⟨ cong (λ x → weaken t [ x , q ]) (sym $ map-wk-p) ⟩
  weaken t [ σ ∘ p , q ]  ≡⟨ cong (_[ σ ∘ p , q ]) (wk-sub-p {t = t}) ⟩
  t [ p ] [ σ ∘ p , q ]   ≡⟨ sym $ subComp t ⟩
  t [ p ∘ (σ ∘ p , q) ]   ≡⟨ cong (t [_]) p-∘ ⟩
  t [ σ ∘ p ]             ≡⟨ subComp t ⟩
  (t [ σ ]) [ p ]         ≡⟨ sym $ wk-sub-p {t = t [ σ ]} ⟩
  weaken (t [ σ ])
  ∎ 

map-var-∘ : ∀ {m n k} (ρ : Ren m n) (ρ' : Ren k m) → map var ρ ∘ map var ρ' ≡ map var (ρ ∙ ρ')
map-var-∘ ρ ρ' =
 let map-ρ  = map var ρ
     map-ρ' = map var ρ'
 in begin
   map-ρ ∘ map-ρ'                       ≡⟨⟩
   map (_[ map-ρ' ]) map-ρ              ≡⟨ sym $ map-∘ (_[ map-ρ' ]) var ρ ⟩
   map (λ x → var x [ map-ρ' ]) ρ       ≡⟨ map-cong (λ x → Ren.lookup-map x var ρ') ρ ⟩
   map (λ x → var x / ρ') ρ             ≡⟨⟩
   map (λ x → var (lookup x ρ')) ρ      ≡⟨ map-∘ var (λ z → lookup z ρ') ρ ⟩
   map var (map (λ i → i Ren./ ρ') ρ)   ≡⟨⟩
   map var (ρ ∙ ρ')
   ∎

weaken-map-var : ∀ {m n} t (ρ : Ren m n) → weaken (t [ map var ρ ]) ≡ t [ map var $ map suc ρ ]
weaken-map-var t ρ = begin
  weaken (t [ map var ρ ])  ≡⟨ wk-sub-p {t = t [ map var ρ ]} ⟩
  (t [ map var ρ ]) [ p ]   ≡⟨ sym $ subComp t ⟩
  t [ map var ρ ∘ p ]       ≡⟨ cong (t [_]) (map-var-∘ ρ Ren.p) ⟩
  t [ map var (ρ ∙ Ren.p) ] ≡⟨ cong (λ x → t [ map var x ]) Ren.map-suc-p ⟩
  t [ map var $ map suc ρ ]
  ∎

weaken-sub-ext : ∀ {n m} t A (γ : Sub m n) → weaken A [ γ , t ] ≡ A [ γ ]
weaken-sub-ext t A γ = begin
    (weaken A) [ γ , t ]  ≡⟨ cong (_[ γ , t ]) (wk-sub-p {t = A}) ⟩
    A [ p ] [ γ , t ]     ≡⟨ sym $ subComp A ⟩
    A [ p ∘ (γ , t) ]     ≡⟨ cong (A [_]) p-∘ ⟩
    A [ γ ]     
    ∎

weaken-map-wk : ∀ {m n} t (γ : Sub m n) → weaken (t [ γ ]) ≡ t [ map weaken γ ]
weaken-map-wk t γ = begin
  weaken (t [ γ ])    ≡⟨⟩
  (t [ γ ]) / Ren.p   ≡⟨ /-map-var Ren.p (t [ γ ]) ⟩
  t [ γ ] [ p ]       ≡⟨ sym $ subComp t ⟩
  t [ γ ∘ p ]         ≡⟨ cong (t [_]) map-wk-p ⟩
  t [ map weaken γ ]
  ∎
  
-- Beta-eta convertibility defined as an inductive relation over lambda terms

infix 5 _~βη_
infix 5 _≈βη_

data _~βη_  {n} : (_ _ : Tm n) → Set where

  varcong : ∀ i → var i ~βη var i
  
  apcong : ∀ {t u t′ u′}
           → t ~βη t′
           → u ~βη u′
           → app t u ~βη app t′ u′
               
  ξ : {t u : Tm (1 + n)} → t ~βη u → ƛ t ~βη ƛ u

  Πcong : ∀ {A A' : Tm n} {B B'}
          → A ~βη A'
          → B ~βη B'
          → Π A B ~βη Π A' B'
               
  β : ∀ {t : Tm (1 + n)} {u} → app (ƛ t) u ~βη t [ id , u ]
               
  η : ∀ {t} → ƛ (app (weaken t) q) ~βη t
  
  sym~βη : ∀ {t₁ t₂}
           → t₁ ~βη t₂
           → t₂ ~βη t₁
               
  trans~βη : ∀ {t₁ t₂ t₃}
             → t₁ ~βη t₂
             → t₂ ~βη t₃
             → t₁ ~βη t₃

-- Relation for substitutions

data _≈βη_ {m} : ∀ {n} (_ _ : Sub m n) → Set where

  ⋄ : ∀ {σ σ' : Sub m 0} → σ ≈βη σ'

  ext : ∀ {n} {t t'} {σ σ' : Sub m n}
        → t ~βη t'
        → σ ≈βη σ'
        → (σ , t) ≈βη (σ' , t')

refl~βη : ∀ {n} {t : Tm n} → t ~βη t
refl~βη = trans~βη (sym~βη η) η

refl≈βη : ∀ {m n} {σ : Sub m n} → σ ≈βη σ
refl≈βη {σ = []}    = ⋄
refl≈βη {σ = _ ∷ _} = ext refl~βη refl≈βη

sym≈βη : ∀ {m n} {σ σ' : Sub m n} → σ ≈βη σ' → σ' ≈βη σ
sym≈βη ⋄            = ⋄
sym≈βη (ext x σ~σ') = ext (sym~βη x) (sym≈βη σ~σ')

trans≈βη : ∀ {m n} {σ₁ σ₂ σ₃ : Sub m n} → σ₁ ≈βη σ₂ → σ₂ ≈βη σ₃ → σ₁ ≈βη σ₃
trans≈βη ⋄              _            = ⋄
trans≈βη (ext x σ₁≈σ₂) (ext y σ₂≈σ₃) = ext (trans~βη x y) (trans≈βη σ₁≈σ₂ σ₂≈σ₃)

~βηequiv : ∀ {n} → IsEquivalence (_~βη_ {n})
~βηequiv = record { refl  = refl~βη
                  ; sym   = sym~βη
                  ; trans = trans~βη
                  }

Tm-βη-Setoid : ∀ {n} → Setoid _ _ 
Tm-βη-Setoid {n} = record { Carrier = Tm n
                          ; _≈_ = _~βη_
                          ; isEquivalence = ~βηequiv
                          }

≈βηequiv : ∀ {m n} → IsEquivalence (_≈βη_ {m} {n})
≈βηequiv = record { refl  = refl≈βη
                  ; sym   = sym≈βη
                  ; trans = trans≈βη
                  }

Sub-βη-Setoid : ∀ {m n} → Setoid _ _
Sub-βη-Setoid {m} {n} = record { Carrier = Sub m n
                               ; _≈_ = _≈βη_
                               ; isEquivalence = ≈βηequiv
                               }

≡-to~βη : ∀ {n} {t u : Tm n} → t ≡ u → t ~βη u
≡-to~βη refl = refl~βη

≡-to-≈βη : ∀ {m n} {σ τ : Sub m n} → σ ≡ τ → σ ≈βη τ
≡-to-≈βη refl = refl≈βη         

lookup-p~ : ∀ {n} (i : Fin n) → lookup i p ~βη var (suc i)
lookup-p~ i = ≡-to~βη (lookup-p i)

-- congruence rules for beta-eta relation

lookup-sub : ∀ {m n} {ρ ρ' : Sub m n} i
             → ρ ≈βη ρ'
             → lookup i ρ ~βη lookup i ρ'
lookup-sub ()      ⋄
lookup-sub zero    (ext t~u _)  = t~u
lookup-sub (suc i) (ext _ ρ≈ρ') = lookup-sub i ρ≈ρ'

congSub-tm : ∀ {m n} {t t'} {σ : Sub m n} → t ~βη t' → t [ σ ] ~βη t' [ σ ]
congSub-tm (varcong i)           = lookup-sub i refl≈βη
congSub-tm (apcong t~t' t~t'')   = apcong (congSub-tm t~t') (congSub-tm t~t'')
congSub-tm (ξ t~t')              = ξ (congSub-tm t~t')
congSub-tm (Πcong A~A' B~B')     = Πcong (congSub-tm A~A') (congSub-tm B~B')
congSub-tm (sym~βη t~t')         = sym~βη (congSub-tm t~t')
congSub-tm (trans~βη t~t' t~t'') = trans~βη (congSub-tm t~t') (congSub-tm t~t'')
congSub-tm {σ = σ} (η {t})
  rewrite sym (prop-η t σ)       = η
congSub-tm {σ = σ} (β {t} {u})
  rewrite prop-β {σ = σ} {u} {t} = β {t = t [ ↑ σ ]} {u = u [ σ ]} 

cong-∘₁ : ∀ {m n k} {σ σ' : Sub m n} {γ : Sub k m}
          → σ ≈βη σ'
          → σ ∘ γ ≈βη σ' ∘ γ
cong-∘₁ {σ = []} {[]} ⋄              = refl≈βη
cong-∘₁ {γ = γ}      (ext t~t' σ≈σ') = ext (congSub-tm t~t') (cong-∘₁ σ≈σ')          

cong-↑ : ∀ {m n} {σ σ' : Sub m n} → σ ≈βη σ' → ↑ σ ≈βη ↑ σ'
cong-↑ {σ = σ} {σ'} σ≈σ'
  rewrite sym $ map-wk-p {σ = σ }
        | sym $ map-wk-p {σ = σ'} = ext refl~βη (cong-∘₁ σ≈σ')

congSub-s : ∀ {m n} {t} {σ σ' : Sub m n} → σ ≈βη σ' → t [ σ ] ~βη t [ σ' ]
congSub-s {σ = []} {[]}     ⋄            = refl~βη
congSub-s {t = var zero}    (ext x _)    = x
congSub-s {t = var (suc i)} (ext x σ≈σ') = congSub-s {t = var i} σ≈σ'
congSub-s {t = app f t}     (ext x σ≈σ') = apcong (congSub-s {t = f} (ext x σ≈σ')) (congSub-s {t = t} (ext x σ≈σ'))
congSub-s {t = ƛ b}         (ext x σ≈σ') = ξ $ congSub-s {t = b} (cong-↑ $ ext x σ≈σ')
congSub-s {t = Π A B}       (ext x σ≈σ') = Πcong (congSub-s {t = A} (ext x σ≈σ')) (congSub-s {t = B} (cong-↑ (ext x σ≈σ')))
congSub-s {t = U}           (ext x σ≈σ') = refl~βη

cong-sub : ∀ {m n} {t t'} {σ σ' : Sub m n}
           → t ~βη t'
           → σ ≈βη σ'
           → t [ σ ] ~βη t' [ σ' ]
cong-sub {t' = t'} t~t' σ≈σ' = trans~βη (congSub-tm t~t') (congSub-s {t = t'} σ≈σ')

cong-∘ : ∀ {m n k} {ρ σ : Sub m n} {ρ' σ' : Sub k m}
         → ρ ≈βη σ
         → ρ' ≈βη σ'
         → ρ ∘ ρ' ≈βη σ ∘ σ'
cong-∘ ⋄           _             = ⋄
cong-∘ (ext t ρ≈σ) ⋄             = ext (cong-sub t ⋄) (cong-∘ ρ≈σ ⋄)
cong-∘ (ext t ρ≈σ) (ext u ρ'≈σ') = ext (cong-sub t (ext u ρ'≈σ')) (cong-∘ ρ≈σ (ext u ρ'≈σ'))

-- ucwf instantiations

ImpSubUcwf : Ucwf
ImpSubUcwf = record
                  { Tm        = Tm
                  ; Sub       = Sub
                  ; _~_       = _~βη_
                  ; _≈_       = _≈βη_
                  ; IsEquivT  = ~βηequiv
                  ; IsEquivS  = ≈βηequiv
                  ; id        = id
                  ; _∘_       = _∘_
                  ; _[_]      = _[_]
                  ; <>        = []
                  ; <_,_>     = _,_
                  ; p         = p
                  ; q         = q
                  ; id-zero   = refl≈βη
                  ; left-zero = refl≈βη
                  ; idExt     = refl≈βη
                  ; idL       = ≡-to-≈βη idL
                  ; idR       = ≡-to-≈βη idR
                  ; assoc     = ≡-to-≈βη ∘-asso
                  ; subId     = ≡-to~βη subId
                  ; pCons     = ≡-to-≈βη p-∘
                  ; qCons     = refl~βη
                  ; subComp   = λ {_} {_} {_} {t} → ≡-to~βη $ subComp t
                  ; compExt   = refl≈βη
                  ; cong-<,>  = ext
                  ; cong-sub  = cong-sub
                  ; cong-∘    = cong-∘
                  }

subLam : ∀ {n m} {σ : Sub m n} {t}
         → ƛ (t [ ↑ σ ]) ~βη ƛ (t [ (σ ∘ p , q) ])
subLam {σ = σ} {t} rewrite sym $ map-wk-p {σ = σ} = refl~βη

η' : ∀ {n} {t : Tm n} → ƛ (app (t [ p ]) q) ~βη t
η' {t = t} rewrite sym $ wk-sub-p {t = t} = η

-- λβη-ucwf instantiation

ImpSubLamUcwf : λβη-ucwf
ImpSubLamUcwf = record
                    { ucwf     = ImpSubUcwf
                    ; lam      = ƛ
                    ; app      = app
                    ; subApp   = refl~βη
                    ; subLam   = λ {n} {m} {σ} {t} → subLam {n} {m} {σ} {t}
                    ; β        = β
                    ; η        = η'
                    ; cong-lam = ξ
                    ; cong-app = apcong
                    }
                    
open import ExtDepTyped.Raw.PiUcwf

subΠ : ∀ {m n} {γ : Sub m n} {A B} → Π (A [ γ ]) (B [ ↑ γ ]) ~βη Π (A [ γ ]) (B [ γ ∘ p , q ])
subΠ {γ = γ} {A} {B} rewrite map-wk-p {σ = γ} = refl~βη

ImpSubΠUcwf : Π-λβη-ucwf
ImpSubΠUcwf = record
                { λucwf  = ImpSubLamUcwf
                ; Π      = Π
                ; U      = U
                ; subU   = refl~βη
                ; subΠ   = λ {m} {n} {γ} {A} {B} → subΠ {m} {n} {γ} {A} {B}
                ; cong-Π = Πcong
                }
