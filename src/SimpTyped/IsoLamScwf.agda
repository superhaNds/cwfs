module SimpTyped.IsoLamScwf where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_] ; lookup)
open import Data.Product hiding (<_,_> ; map)
open import Relation.Binary
open import Function as F using (_$_ ; flip)
open import Relation.Binary.PropositionalEquality as P hiding ([_] ; cong-app ; cong-∘)
import Relation.Binary.Reasoning.Setoid as EqR

open import SimpTyped.Type renaming (⋄ to ε)
open import SimpTyped.Scwf
open import SimpTyped.ExpSubLam as Exp renaming (Tm to Tm-cwf ; Sub to Sub-cwf ; q to q⋆ ; p to p⋆ ; id to id⋆ ; _∘_ to _∘⋆_ ; _[_] to _[_]⋆)
open import SimpTyped.ImpSubLam as Imp renaming (Tm to Tm-λ ; Sub to Sub-λ) hiding (subComp ; cong-∘₁ ; cong-∘ ; subLam)


-- Transform a term/substitution from an explicit to an implicit

⟦_⟧  : ∀ {n A} {Γ : Ctx n} → Tm-cwf Γ A → Tm-λ Γ A
⟦_⟧' : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → Sub-cwf Δ Γ → Sub-λ Δ Γ

⟦ q⋆       ⟧ = q
⟦ t [ γ ]⋆ ⟧ = ⟦ t ⟧ [ ⟦ γ ⟧' ]
⟦ app f t  ⟧ = app ⟦ f ⟧ ⟦ t ⟧
⟦ lam t    ⟧ = ƛ ⟦ t ⟧

⟦ <>        ⟧' = <>
⟦ id⋆       ⟧' = id
⟦ p⋆        ⟧' = p
⟦ γ₁ ∘⋆ γ₂  ⟧' = ⟦ γ₁ ⟧' ∘ ⟦ γ₂ ⟧'
⟦ < γ , t > ⟧' = < ⟦ γ ⟧' , ⟦ t ⟧ >

-- Maps a scoped variable to a variable built with explicit subistutions

var⋆ : ∀ {n A} {Γ : Ctx n} (v : Var Γ A) → Tm-cwf Γ A
var⋆ {Γ = []}    (()    , _)
var⋆ {Γ = _ ∷ _} (zero  , refl) = q⋆
var⋆ {Γ = _ ∷ _} (suc i , refl) = var⋆ (i , refl) [ p⋆ ]⋆

-- Transform a term/substitution from an implicit to an explicit

⟪_⟫  : ∀ {n A} {Γ : Ctx n} → Tm-λ Γ A → Tm-cwf Γ A
⟪_⟫' : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → Sub-λ Δ Γ → Sub-cwf Δ Γ

⟪ var v   ⟫ = var⋆ v
⟪ ƛ t     ⟫ = lam ⟪ t ⟫
⟪ app f t ⟫ = app ⟪ f ⟫ ⟪ t ⟫

⟪ <>        ⟫' = <>
⟪ < γ , t > ⟫' = < ⟪ γ ⟫' , ⟪ t ⟫ >

vars⋆ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} → Ren Δ Γ → Sub-cwf Δ Γ
vars⋆ <>        = <>
vars⋆ < ρ , v > = < vars⋆ ρ , var⋆ v >

-- Supporting lemmas with particular focus on the relationship between implicit renamings and explicit substitutions 

var⋆-wk-p⋆ : ∀ {n A A'} {Γ : Ctx n} (v : Var Γ A') →
             var⋆ v  [ p⋆ {A = A} {Γ = Γ} ]⋆ ~ var⋆ (Ren.weaken v)
var⋆-wk-p⋆ {Γ = _ ∷ _} (zero , refl)  = refl~
var⋆-wk-p⋆ {Γ = _ ∷ _} (suc i , refl) = refl~

var-lemma : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ)
            → vars⋆ ρ ∘⋆ p⋆ {A = A} ≈ vars⋆ (++ᵣ ρ)
var-lemma <>        = left-zero
var-lemma < ρ , v > = begin
  < vars⋆ ρ , var⋆ v > ∘⋆ p⋆         ≈⟨ compExt ⟩
  < vars⋆ ρ ∘⋆ p⋆ , var⋆ v [ p⋆ ]⋆ > ≈⟨ cong-<,> refl~ (var-lemma ρ) ⟩
  < vars⋆ (++ᵣ ρ) , var⋆ v [ p⋆ ]⋆ > ≈⟨ cong-<,> (var⋆-wk-p⋆ v) refl≈ ⟩
  < vars⋆ (++ᵣ ρ) , var⋆ (Ren.weaken v) > ∎
  where open EqR (SubSetoid {_} {_})

p⋆-norm : ∀ {n A} {Γ : Ctx n} → Sub-cwf (Γ ∙ A) Γ
p⋆-norm = vars⋆ Ren.p

p⋆≈p⋆-norm : ∀ {n A} {Γ : Ctx n} → p⋆ {A = A} {Γ = Γ} ≈ vars⋆ (Ren.p)
p⋆≈p⋆-norm {n = zero} {A}  {[]} = emptySub p⋆
p⋆≈p⋆-norm {n = suc n} {A} {_ ∷ Γ} = begin
  p⋆                                   ≈⟨ surj-<,> p⋆ ⟩
  < p⋆ ∘⋆ p⋆ , q⋆ [ p⋆ ]⋆ >            ≈⟨ cong-<,> refl~ (cong-∘ p⋆≈p⋆-norm refl≈) ⟩
  < vars⋆ Ren.p ∘⋆ p⋆ , q⋆ [ p⋆ ]⋆ >   ≈⟨ cong-<,> refl~ (var-lemma Ren.p) ⟩  
  < vars⋆ (++ᵣ Ren.p) , q⋆ [ p⋆ ]⋆ >
  ∎
  where open EqR (SubSetoid {_} {_})

ren→vars⋆ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (ρ : Ren Δ Γ) → ⟪ renToSub ρ ⟫' ≈ vars⋆ ρ
ren→vars⋆ <>        = refl≈
ren→vars⋆ < ρ , _ > = cong-<,> refl~ (ren→vars⋆ ρ)

--------- Preservation properties when going through a cwf morphism -----------------------------------

p-preserved : ∀ {n A} {Γ : Ctx n} → ⟪ p {A = A} {Γ} ⟫' ≈ p⋆
p-preserved = begin
  ⟪ p ⟫'       ≈⟨ ren→vars⋆ Ren.p ⟩
  vars⋆ Ren.p  ≈⟨ sym≈ $ p⋆≈p⋆-norm ⟩
  p⋆
  ∎
  where open EqR (SubSetoid {_} {_})

id-preserved : ∀ {n} {Γ : Ctx n} → ⟪ id {Γ = Γ} ⟫' ≈ id⋆
id-preserved {zero}  {[]}    = sym≈ id-zero
id-preserved {suc n} {_ ∷ Γ} = begin
  < ⟪ p ⟫' , q⋆ > ≈⟨ cong-<,> refl~ p-preserved ⟩
  < p⋆ , q⋆ >     ≈⟨ sym≈ idExt ⟩
  id⋆
  ∎
  where open EqR (SubSetoid {_} {_})

ren-preserves : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (t : Tm-λ Γ A) (ρ : Ren Δ Γ)
                → ⟪ t / ρ ⟫ ~ ⟪ t ⟫ [ vars⋆ ρ ]⋆
ren-preserves (var (zero , refl))  < ρ , _ > = sym~ qCons
ren-preserves (var (suc i , refl)) < ρ , x > = begin
  var⋆ ((i , refl) Ren./ ρ)                         ≈⟨ ren-preserves (var (i , refl)) ρ ⟩
  var⋆ (i , refl) [ vars⋆ ρ ]⋆                      ≈⟨ _~_.cong-sub refl~ (sym≈ (pCons (vars⋆ ρ))) ⟩
  var⋆ (i , refl) [ p⋆ ∘⋆ < vars⋆ ρ , var⋆ x > ]⋆   ≈⟨ subComp (var⋆ (i , refl)) ⟩
  var⋆ (i , refl) [ p⋆ ]⋆ [ < vars⋆ ρ , var⋆ x > ]⋆
  ∎
  where open EqR (TmSetoid {_} {_})
ren-preserves (app f t) ρ = trans~ (cong-app (ren-preserves f ρ) (ren-preserves t ρ)) subApp
ren-preserves (ƛ t) ρ = begin
  lam ⟪ t / Ren.↑ ρ ⟫                     ≈⟨ cong-lam (ren-preserves t (Ren.↑ ρ)) ⟩
  lam (⟪ t ⟫ [ < vars⋆ (++ᵣ ρ) , q⋆ > ]⋆) ≈⟨ cong-lam (_~_.cong-sub refl~ (cong-<,> refl~ (sym≈ (var-lemma ρ)))) ⟩
  lam (⟪ t ⟫ [ < vars⋆ ρ ∘⋆ p⋆ , q⋆ > ]⋆) ≈⟨ sym~ subLam ⟩
  lam ⟪ t ⟫ [ vars⋆ ρ ]⋆ 
  ∎
  where open EqR (TmSetoid {_} {_})

wk-⟪⟫ : ∀ {n A A'} {Γ : Ctx n} (t : Tm-λ Γ A) → ⟪ weaken {A' = A'} t ⟫ ~ ⟪ t ⟫ [ p⋆ ]⋆
wk-⟪⟫ {A = A} {A'} {Γ} (var x)
  rewrite wk-ren-eq {B = A'} {Γ = Γ} Ren.id x
        | renId {Γ = Γ} x = sym~ (var⋆-wk-p⋆ x)
wk-⟪⟫ (app f t) = trans~ (cong-app (wk-⟪⟫ f) (wk-⟪⟫ t)) subApp
wk-⟪⟫ (ƛ t) = begin
  lam ⟪ t / Ren.↑ Ren.p ⟫                       ≈⟨ cong-lam $ ren-preserves t (Ren.↑ Ren.p) ⟩
  lam (⟪ t ⟫ [ < vars⋆ (++ᵣ Ren.p) , q⋆ > ]⋆)   ≈⟨ cong-lam $ _~_.cong-sub refl~ $ cong-<,> refl~ (sym≈ $ var-lemma Ren.p) ⟩
  lam (⟪ t ⟫ [ < vars⋆ (Ren.p) ∘⋆ p⋆ , q⋆ > ]⋆) ≈⟨ cong-lam $ _~_.cong-sub refl~ $ cong-<,> refl~ (cong-∘ (sym≈ p⋆≈p⋆-norm) refl≈) ⟩
  lam (⟪ t ⟫ [ < p⋆ ∘⋆ p⋆ , q⋆ > ]⋆)            ≈⟨ sym~ subLam ⟩
  ⟪ ƛ t ⟫ [ p⋆ ]⋆
  ∎
  where open EqR (TmSetoid {_} {_})

wk-sub-⟪⟫ : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub-λ Δ Γ) → ⟪ ++ₜ {A = A} γ ⟫' ≈ ⟪ γ ⟫' ∘⋆ p⋆
wk-sub-⟪⟫ <>        = sym≈ left-zero
wk-sub-⟪⟫ < γ , t > = trans≈ (cong-<,> (wk-⟪⟫ t) (wk-sub-⟪⟫ γ)) (sym≈ compExt)

sub-preserved : ∀ {m n A} {Δ : Ctx m} {Γ : Ctx n}
                  (t : Tm-λ Γ A) (γ : Sub-λ Δ Γ)
                → ⟪ t [ γ ] ⟫ ~ ⟪ t ⟫ [ ⟪ γ ⟫' ]⋆
sub-preserved (var (zero , refl))  < _ , _ > = sym~ qCons
sub-preserved (var (suc i , refl)) < γ , x > = let v = (i , refl) in begin
  ⟪ v Ren./ γ ⟫                            ≈⟨ sub-preserved (var v) γ ⟩
  var⋆ v [ ⟪ γ ⟫' ]⋆                       ≈⟨ _~_.cong-sub refl~ (sym≈ $ pCons ⟪ γ ⟫') ⟩
  var⋆ v [ p⋆ ∘⋆ < ⟪ γ ⟫' , ⟪ x ⟫ > ]⋆     ≈⟨ subComp (var⋆ (i , refl)) ⟩
  (var⋆ v [ p⋆ ]⋆) [ < ⟪ γ ⟫' , ⟪ x ⟫ > ]⋆
  ∎
  where open EqR (TmSetoid {_} {_})
sub-preserved (app f t) γ = trans~ (cong-app (sub-preserved f γ) (sub-preserved t γ))
                                   subApp
sub-preserved (ƛ t)     γ = begin
  lam ⟪ t [ ↑ γ ] ⟫                       ≈⟨ cong-lam (sub-preserved t (↑ γ)) ⟩
  lam (⟪ t ⟫ [ < ⟪ ++ₜ γ ⟫' , q⋆ > ]⋆)    ≈⟨ cong-lam $ _~_.cong-sub refl~ $ cong-<,> refl~ (wk-sub-⟪⟫ γ) ⟩
  lam (⟪ t ⟫ [ < ⟪ γ ⟫' ∘⋆ p⋆  , q⋆ > ]⋆) ≈⟨ sym~ subLam ⟩
  lam ⟪ t ⟫ [ ⟪ γ ⟫' ]⋆
  ∎
  where open EqR (TmSetoid {_} {_})

∘-preserved : ∀ {m n k} {E : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
                (γ₁ : Sub-λ E Γ) (γ₂ : Sub-λ Δ E)
              → ⟪ γ₁ ∘ γ₂ ⟫' ≈ ⟪ γ₁ ⟫' ∘⋆ ⟪ γ₂ ⟫'
∘-preserved <>         _  = sym≈ left-zero
∘-preserved < γ₁ , x > γ₂ = trans≈ (cong-<,> (sub-preserved x γ₂) (∘-preserved γ₁ γ₂))
                                   (sym≈ compExt)

---------------------- Inverse lemmas, proof of Isomorphism -------------------------------------

left-inv-tm : ∀ {n A} {Γ : Ctx n} (t : Tm-cwf Γ A) → ⟪ ⟦ t ⟧ ⟫ ~ t
left-inv-sub : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub-cwf Δ Γ) → ⟪ ⟦ γ ⟧' ⟫' ≈ γ

left-inv-tm q⋆         = refl~
left-inv-tm (app f t)  = cong-app (left-inv-tm f) (left-inv-tm t)
left-inv-tm (lam t)    = cong-lam (left-inv-tm t)
left-inv-tm (t [ γ ]⋆) = begin
  ⟪ ⟦ t ⟧ [ ⟦ γ ⟧' ] ⟫       ≈⟨ sub-preserved ⟦ t ⟧ ⟦ γ ⟧' ⟩
  ⟪ ⟦ t ⟧ ⟫ [ ⟪ ⟦ γ ⟧' ⟫' ]⋆ ≈⟨ _~_.cong-sub (left-inv-tm t) refl≈ ⟩
  t [ ⟪ ⟦ γ ⟧' ⟫' ]⋆         ≈⟨ _~_.cong-sub refl~ (left-inv-sub γ) ⟩
  t [ γ ]⋆
  ∎
  where open EqR (TmSetoid {_})

left-inv-sub <>         = refl≈
left-inv-sub id⋆        = id-preserved
left-inv-sub p⋆         = p-preserved
left-inv-sub < γ , t >  = cong-<,> (left-inv-tm t) (left-inv-sub γ)
left-inv-sub (γ₁ ∘⋆ γ₂) = begin
  ⟪ ⟦ γ₁ ⟧' ∘ ⟦ γ₂ ⟧' ⟫'        ≈⟨ ∘-preserved ⟦ γ₁ ⟧' ⟦ γ₂ ⟧' ⟩
  ⟪ ⟦ γ₁ ⟧' ⟫' ∘⋆ ⟪ ⟦ γ₂ ⟧' ⟫'  ≈⟨ cong-∘ (left-inv-sub γ₁) refl≈ ⟩
  γ₁ ∘⋆ ⟪ ⟦ γ₂ ⟧' ⟫'            ≈⟨ cong-∘ refl≈ (left-inv-sub γ₂) ⟩
  γ₁ ∘⋆ γ₂
  ∎
  where open EqR (SubSetoid {_} {_})

right-inv-tm : ∀ {n A} {Γ : Ctx n} (t : Tm-λ Γ A) → ⟦ ⟪ t ⟫ ⟧ ~βη t
right-inv-tm (ƛ t)     = ξ $ right-inv-tm t
right-inv-tm (app f t) = apcong (right-inv-tm f) (right-inv-tm t)
right-inv-tm {Γ = x ∷ Γ} (var (zero , refl))  = refl~βη
right-inv-tm {Γ = x ∷ Γ} (var (suc i , refl)) = begin
  ⟦ var⋆ (i , refl) ⟧ [ p ] ≈⟨ congSub-tm {Γ = Γ} (right-inv-tm (var (i , refl))) ⟩
  var (i , refl) [ p ]      ≈⟨ sub-p-wk~ $ var (i , refl) ⟩
  weaken (var (i , refl))   ≈⟨ ≡-to~βη (sym wk-var) ⟩
  var (suc i , refl)
  ∎
  where open EqR (Tm-βη-Setoid {_})

right-inv-sub : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} (γ : Sub-λ Δ Γ) → ⟦ ⟪ γ ⟫' ⟧' ≈βη γ
right-inv-sub <>        = refl≈βη
right-inv-sub < γ , t > = ext (right-inv-tm t) (right-inv-sub γ)

