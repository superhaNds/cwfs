module Iso-LamUcwf where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_])
open import Relation.Binary
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as P hiding ([_] ; cong-app)
import Relation.Binary.EqReasoning as EqR

open import Ucwf
open import ExpSubLam renaming (Tm to Tm-cwf ; Sub to Sub-cwf ; q to q⋆ ; p to p⋆ ; id to id⋆ ; _∘_ to _∘⋆_ ; _[_] to _[_]⋆)
open import ImpSubLam renaming (Tm to Tm-λ ; Sub to Sub-λ) hiding (subComp ; idExt ; p-∘ ; cong-∘₁ ; subLam)
open import ImpSub as Ren using (Ren)

⟦_⟧  : ∀ {n} → Tm-cwf n → Tm-λ n
⟦_⟧' : ∀ {m n} → Sub-cwf m n → Sub-λ m n

⟦ q⋆ ⟧       = q
⟦ t [ σ ]⋆ ⟧ = ⟦ t ⟧ [ ⟦ σ ⟧' ]
⟦ app f t ⟧  = app ⟦ f ⟧ ⟦ t ⟧
⟦ ƛ t ⟧      = ƛ ⟦ t ⟧

⟦ id⋆ ⟧'       = id
⟦ p⋆ ⟧'        = p
⟦ <> ⟧'        = []
⟦ σ₁ ∘⋆ σ₂ ⟧'  = ⟦ σ₁ ⟧' ∘ ⟦ σ₂ ⟧'
⟦ < σ , t > ⟧' = ⟦ σ ⟧' , ⟦ t ⟧

varExp : ∀ {n} (i : Fin n) → Tm-cwf n
varExp zero = q⋆
varExp (suc i) = varExp i [ p⋆ ]⋆

⟪_⟫  : ∀ {n} → Tm-λ n → Tm-cwf n
⟪_⟫' : ∀ {m n} → Sub-λ m n → Sub-cwf m n

⟪ var i ⟫   = varExp i
⟪ app f t ⟫ = app ⟪ f ⟫ ⟪ t ⟫
⟪ ƛ t ⟫     = ƛ ⟪ t ⟫

⟪ [] ⟫'    = <>
⟪ t ∷ σ ⟫' = < ⟪ σ ⟫' , ⟪ t ⟫ >

ExpSubUcwf⇒ : Ucwf-⇒ ExpSubUcwf ImpSubUcwf
ExpSubUcwf⇒ = record
                { ⟦_⟧           = ⟦_⟧
                ; ⟦_⟧'          = ⟦_⟧'
                ; id-preserved  = refl≈βη
                ; q-preserved   = refl~βη
                ; p-preserved   = refl≈βη
                ; ∘-preserved   = λ σ₁ σ₂ → refl≈βη
                ; <>-preserved  = refl≈βη
                ; <,>-preserved = λ t σ → refl≈βη
                ; sub-preserved = λ t σ → refl~βη
                }

λExpSubUcwf⇒ : λβη-ucwf-⇒ ExpSubLamUcwf ImpSubLamUcwf
λExpSubUcwf⇒ = record { ucwf-⇒        = ExpSubUcwf⇒
                      ; lam-preserved = refl~βη
                      ; app-preserved = refl~βη
                      }

module Proj where

  varsExp : ∀ {m n} → Ren m n → Sub-cwf m n
  varsExp []      = <>
  varsExp (i ∷ ρ) = < varsExp ρ , varExp i >

  var-lemma : ∀ {m n} (ρ : Ren m n) → varsExp ρ ∘⋆ p⋆ ≈ varsExp (map suc ρ)
  var-lemma []      = left-zero
  var-lemma (i ∷ ρ) = begin
    < varsExp ρ , varExp i > ∘⋆ p⋆              ≈⟨ compExt ⟩
    < varsExp ρ ∘⋆ p⋆ , varExp i [ p⋆ ]⋆ >      ≈⟨ cong-<, (var-lemma ρ) ⟩
    < varsExp (map suc ρ) , varExp i [ p⋆ ]⋆ >
    ∎
    where open EqR (SubSetoid {_} {_})

  p⋆-norm : ∀ {n} → Sub-cwf (suc n) n
  p⋆-norm {n} = varsExp Ren.p

  p⋆≈p⋆-norm : ∀ {n} → p⋆ {n} ≈ varsExp (Ren.p)
  p⋆≈p⋆-norm {zero}  = emptySub _
  p⋆≈p⋆-norm {suc n} = begin
    p⋆                                        ≈⟨ surj-<,> p⋆ ⟩
    < p⋆ ∘⋆ p⋆ , q⋆ [ p⋆ ]⋆ >                 ≈⟨ cong-<, (cong-∘₁ p⋆≈p⋆-norm) ⟩
    < varsExp Ren.p ∘⋆ p⋆ , q⋆ [ p⋆ ]⋆ >      ≈⟨ cong-<, (var-lemma Ren.p) ⟩
    < varsExp (map suc Ren.p) , q⋆ [ p⋆ ]⋆ > 
    ∎
    where open EqR (SubSetoid {_} {_})

  vars-any : ∀ {m n} (ρ : Ren m n) → ⟪ map var ρ ⟫' ≈ varsExp ρ
  vars-any []      = refl≈
  vars-any (_ ∷ ρ) = cong-<, (vars-any ρ)

  vars-p : ∀ {n} → ⟪ p {n} ⟫' ≈ varsExp Ren.p
  vars-p = vars-any Ren.p

p-preserved : ∀ {n} → ⟪ p {n} ⟫' ≈ p⋆
p-preserved = trans≈ Proj.vars-p (sym≈ Proj.p⋆≈p⋆-norm)

id-preserved : ∀ {n} → ⟪ id {n} ⟫' ≈ id⋆
id-preserved {zero}  = sym≈ id-zero
id-preserved {suc n} = begin
  < ⟪ p ⟫' , ⟪ q ⟫ > ≈⟨ cong-<, p-preserved ⟩
  < p⋆ , q⋆ >        ≈⟨ sym≈ idExt ⟩
  id⋆
  ∎
  where open EqR (SubSetoid {_} {_})

wk-⟦⟧ : ∀ {n} (t : Tm-cwf n) → ⟦ t [ p⋆ ]⋆ ⟧ ~βη weaken ⟦ t ⟧
wk-⟦⟧ q⋆ = varcong (suc zero)
wk-⟦⟧ (app f t) rewrite sym (wk-sub-p {t = ⟦ f ⟧})
                      | sym (wk-sub-p {t = ⟦ t ⟧}) = refl~βη
wk-⟦⟧ (ƛ t) rewrite sym $ /-↑-[] {t = ⟦ t ⟧}       = refl~βη
wk-⟦⟧ (t [ σ ]⋆)
  rewrite sym (wk-sub-p {t = ⟦ t ⟧ [ ⟦ σ ⟧' ]})    = refl~βη

wk-⟪⟫ : ∀ {n} (t : Tm-λ n) → ⟪ weaken t ⟫ ~ ⟪ t ⟫ [ p⋆ ]⋆
wk-⟪⟫ (var i) rewrite Ren.lookup-p i = refl~
wk-⟪⟫ (app f t) = begin 
  app ⟪ weaken f ⟫ ⟪ weaken t ⟫       ≈⟨ cong-app (wk-⟪⟫ f) (wk-⟪⟫ t) ⟩
  app (⟪ f ⟫ [ p⋆ ]⋆) (⟪ t ⟫ [ p⋆ ]⋆) ≈⟨ sym~ subApp ⟩
  app ⟪ f ⟫ ⟪ t ⟫ [ p⋆ ]⋆
  ∎
  where open EqR (TmSetoid {_})
wk-⟪⟫ (ƛ t) rewrite /-↑-[] {t = t} = begin
  ƛ ⟪ t [ ↑ p ] ⟫       ≈⟨ {!!} ⟩
  (ƛ ⟪ t ⟫) [ p⋆ ]⋆
  ∎
  where open EqR (TmSetoid {_})

map-wk-⟪⟫ : ∀ {m n} (σ : Sub-λ m n) → ⟪ map weaken σ ⟫' ≈ ⟪ σ ⟫' ∘⋆ p⋆
map-wk-⟪⟫ [] = sym≈ left-zero
map-wk-⟪⟫ (t ∷ σ) = begin
  < ⟪ map weaken σ ⟫' , ⟪ weaken t ⟫ > ≈⟨ cong-<, (map-wk-⟪⟫ σ) ⟩
  < ⟪ σ ⟫' ∘⋆ p⋆ , ⟪ weaken t ⟫ >      ≈⟨ cong-,> (wk-⟪⟫ t) ⟩
  < ⟪ σ ⟫' ∘⋆ p⋆ , ⟪ t ⟫ [ p⋆ ]⋆ >     ≈⟨ sym≈ compExt ⟩
  < ⟪ σ ⟫' , ⟪ t ⟫ > ∘⋆ p⋆
  ∎
  where open EqR (SubSetoid {_} {_})

sub-preserved : ∀ {m n} t (σ : Sub-λ m n) → ⟪ t [ σ ] ⟫ ~ ⟪ t ⟫ [ ⟪ σ ⟫' ]⋆
sub-preserved (var zero)    (t ∷ σ) = sym~ q-sub
sub-preserved (var (suc i)) (t ∷ σ) = begin
  ⟪ lookup i σ ⟫                             ≈⟨ sub-preserved (var i) σ ⟩
  ⟪ var i ⟫ [ ⟪ σ ⟫' ]⋆                      ≈⟨ cong-sub₂ (sym≈ p-∘) ⟩
  ⟪ var i ⟫ [ p⋆ ∘⋆ < ⟪ σ ⟫' , ⟪ t ⟫ > ]⋆    ≈⟨ subComp ⟩
  (⟪ var i ⟫ [ p⋆ ]⋆) [ < ⟪ σ ⟫' , ⟪ t ⟫ > ]⋆
  ∎
  where open EqR (TmSetoid {_})
sub-preserved (app f t) σ = begin
  app ⟪ f [ σ ] ⟫ ⟪ t [ σ ] ⟫                 ≈⟨ cong-app (sub-preserved f σ) (sub-preserved t σ) ⟩
  app (⟪ f ⟫ [ ⟪ σ ⟫' ]⋆) (⟪ t ⟫ [ ⟪ σ ⟫' ]⋆) ≈⟨ sym~ subApp ⟩
  app ⟪ f ⟫ ⟪ t ⟫ [ ⟪ σ ⟫' ]⋆
  ∎
  where open EqR (TmSetoid {_})
sub-preserved (ƛ t) σ = begin
  ƛ ⟪ t [ ↑ σ ] ⟫                           ≈⟨ cong-lam $ sub-preserved t (↑ σ) ⟩
  ƛ (⟪ t ⟫ [ < ⟪ map weaken σ ⟫' , q⋆ > ]⋆) ≈⟨ cong-lam (cong-sub₂ (cong-<, (map-wk-⟪⟫ σ))) ⟩
  ƛ (⟪ t ⟫ [ < ⟪ σ ⟫' ∘⋆ p⋆ , q⋆ > ]⋆)      ≈⟨ sym~ subLam ⟩
  ƛ ⟪ t ⟫ [ ⟪ σ ⟫' ]⋆
  ∎
  where open EqR (TmSetoid {_})

∘-preserved : ∀ {m n k} (σ₁ : Sub-λ k n) (σ₂ : Sub-λ m k)
              → ⟪ σ₁ ∘ σ₂ ⟫' ≈ ⟪ σ₁ ⟫' ∘⋆ ⟪ σ₂ ⟫'
∘-preserved [] _ = sym≈ left-zero
∘-preserved (t ∷ σ₁) σ₂ = begin
  < ⟪ σ₁ ∘ σ₂ ⟫' , ⟪ t [ σ₂ ] ⟫ >             ≈⟨ cong-<, (∘-preserved σ₁ σ₂) ⟩
  < ⟪ σ₁ ⟫' ∘⋆ ⟪ σ₂ ⟫' , ⟪ t [ σ₂ ] ⟫ >       ≈⟨ cong-,> (sub-preserved t σ₂) ⟩
  < ⟪ σ₁ ⟫' ∘⋆ ⟪ σ₂ ⟫' , ⟪ t ⟫ [ ⟪ σ₂ ⟫' ]⋆ > ≈⟨ sym≈ compExt ⟩
  < ⟪ σ₁ ⟫' , ⟪ t ⟫ > ∘⋆ ⟪ σ₂ ⟫'
  ∎
  where open EqR (SubSetoid {_} {_})

ImpSubUcwf⇒ : Ucwf-⇒ ImpSubUcwf ExpSubUcwf
ImpSubUcwf⇒ = record
                { ⟦_⟧           = ⟪_⟫
                ; ⟦_⟧'          = ⟪_⟫'
                ; id-preserved  = id-preserved
                ; q-preserved   = refl~
                ; p-preserved   = p-preserved
                ; ∘-preserved   = ∘-preserved
                ; <>-preserved  = refl≈
                ; <,>-preserved = λ t σ → refl≈
                ; sub-preserved = sub-preserved
                }

λImpSubUcwf⇒ : λβη-ucwf-⇒ ImpSubLamUcwf ExpSubLamUcwf
λImpSubUcwf⇒ = record { ucwf-⇒        = ImpSubUcwf⇒
                      ; lam-preserved = refl~
                      ; app-preserved = refl~
                      }

left-inv-tm : ∀ {n} (t : Tm-cwf n) → ⟪ ⟦ t ⟧ ⟫ ~ t

left-inv-sub : ∀ {m n} (σ : Sub-cwf m n) → ⟪ ⟦ σ ⟧' ⟫' ≈ σ
left-inv-sub id⋆        = id-preserved
left-inv-sub p⋆         = p-preserved
left-inv-sub <>         = refl≈
left-inv-sub < σ , t >  = cong-<,> (left-inv-tm t) (left-inv-sub σ)
left-inv-sub (σ₁ ∘⋆ σ₂) = begin
  ⟪ ⟦ σ₁ ⟧' ∘ ⟦ σ₂ ⟧' ⟫'       ≈⟨ ∘-preserved ⟦ σ₁ ⟧' ⟦ σ₂ ⟧' ⟩
  ⟪ ⟦ σ₁ ⟧' ⟫' ∘⋆ ⟪ ⟦ σ₂ ⟧' ⟫' ≈⟨ cong-∘₁ (left-inv-sub σ₁) ⟩
  σ₁ ∘⋆ ⟪ ⟦ σ₂ ⟧' ⟫'           ≈⟨ cong-∘₂ (left-inv-sub σ₂) ⟩
  σ₁ ∘⋆ σ₂
  ∎
  where open EqR (SubSetoid {_} {_})

left-inv-tm q⋆         = refl~
left-inv-tm (app f t)  = cong-app (left-inv-tm f) (left-inv-tm t)
left-inv-tm (ƛ t)      = cong-lam (left-inv-tm t)
left-inv-tm (t [ σ ]⋆) = begin
  ⟪ ⟦ t ⟧ [ ⟦ σ ⟧' ] ⟫       ≈⟨ sub-preserved ⟦ t ⟧ ⟦ σ ⟧' ⟩
  ⟪ ⟦ t ⟧ ⟫ [ ⟪ ⟦ σ ⟧' ⟫' ]⋆ ≈⟨ cong-sub₁ (left-inv-tm t) ⟩
  t [ ⟪ ⟦ σ ⟧' ⟫' ]⋆         ≈⟨ cong-sub₂ (left-inv-sub σ) ⟩
  t [ σ ]⋆
  ∎
  where open EqR (TmSetoid {_})

right-inv-tm : ∀ {n} (t : Tm-λ n) → ⟦ ⟪ t ⟫ ⟧ ~βη t
right-inv-tm (app f t)     = apcong (right-inv-tm f) (right-inv-tm t)
right-inv-tm (ƛ t)         = ξ (right-inv-tm t)
right-inv-tm (var zero)    = refl~βη
right-inv-tm (var (suc i)) = begin
  ⟦ ⟪ var i ⟫ ⟧ [ p ] ≈⟨ congSub-tm (right-inv-tm (var i)) ⟩
  var i [ p ]         ≈⟨ lookup-p~ i ⟩
  var (suc i)
  ∎
  where open EqR (Tm-βη-Setoid {_})

right-inv-sub : ∀ {m n} (σ : Sub-λ m n) → ⟦ ⟪ σ ⟫' ⟧' ≈βη σ
right-inv-sub []      = refl≈βη
right-inv-sub (t ∷ σ) = ext (right-inv-tm t) (right-inv-sub σ)

ExpSubLamUcwf-ImpSubLamUcwf-≅ : λβη-ucwf-≅ λExpSubUcwf⇒ λImpSubUcwf⇒
ExpSubLamUcwf-ImpSubLamUcwf-≅ = record
                                  { left-inv-tm   = left-inv-tm
                                  ; right-inv-tm  = right-inv-tm
                                  ; left-inv-sub  = left-inv-sub
                                  ; right-inv-sub = right-inv-sub
                                  }
