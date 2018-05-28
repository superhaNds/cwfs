module ExtDepTyped.Raw.Iso-PiUcwf where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_])
open import Relation.Binary
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as P hiding ([_] ; cong-app)
import Relation.Binary.EqReasoning as EqR
open import Unityped.Ucwf
open import ExtDepTyped.Raw.PiUcwf
open import ExtDepTyped.Raw.ExpSub
  renaming (Tm to Tm-cwf ; Sub to Sub-cwf ; q to q⋆ ; p to p⋆ ; id to id⋆ ; _∘_ to _∘⋆_ ; _[_] to _[_]⋆)
open import ExtDepTyped.Raw.ImpSub
  renaming (Tm to Tm-λ ; Sub to Sub-λ) hiding (subComp ; idExt ; p-∘ ; cong-∘₁ ; subLam ; subΠ)
open import Unityped.ImpSub as Ren using (Ren)

⟦_⟧  : ∀ {n}   → Tm-cwf n    → Tm-λ n
⟦_⟧' : ∀ {m n} → Sub-cwf m n → Sub-λ m n

⟦ q⋆ ⟧       = q
⟦ t [ γ ]⋆ ⟧ = ⟦ t ⟧ [ ⟦ γ ⟧' ]
⟦ app f t ⟧  = app ⟦ f ⟧ ⟦ t ⟧
⟦ ƛ t ⟧      = ƛ ⟦ t ⟧
⟦ Π A B ⟧    = Π ⟦ A ⟧ ⟦ B ⟧
⟦ U ⟧        = U

⟦ id⋆ ⟧'       = id
⟦ p⋆ ⟧'        = p
⟦ <> ⟧'        = []
⟦ γ₁ ∘⋆ γ₂ ⟧'  = ⟦ γ₁ ⟧' ∘ ⟦ γ₂ ⟧'
⟦ < γ , t > ⟧' = ⟦ γ ⟧' , ⟦ t ⟧

varExp : ∀ {n} (i : Fin n) → Tm-cwf n
varExp zero    = q⋆
varExp (suc i) = varExp i [ p⋆ ]⋆

⟪_⟫  : ∀ {n} → Tm-λ n → Tm-cwf n
⟪_⟫' : ∀ {m n} → Sub-λ m n → Sub-cwf m n

⟪ var i ⟫   = varExp i
⟪ app f t ⟫ = app ⟪ f ⟫ ⟪ t ⟫
⟪ ƛ t ⟫     = ƛ ⟪ t ⟫
⟪ Π A B ⟫   = Π ⟪ A ⟫ ⟪ B ⟫
⟪ U ⟫       = U

⟪ [] ⟫'    = <>
⟪ t ∷ γ ⟫' = < ⟪ γ ⟫' , ⟪ t ⟫ >

ExpSubUcwf⇒ : Ucwf-⇒ ExpSubUcwf ImpSubUcwf
ExpSubUcwf⇒ = record
                { ⟦_⟧           = ⟦_⟧
                ; ⟦_⟧'          = ⟦_⟧'
                ; id-preserved  = refl≈βη
                ; q-preserved   = refl~βη
                ; p-preserved   = refl≈βη
                ; ∘-preserved   = λ γ₁ γ₂ → refl≈βη
                ; <>-preserved  = refl≈βη
                ; <,>-preserved = λ t γ → refl≈βη
                ; sub-preserved = λ t γ → refl~βη
                }

λExpSubUcwf⇒ : λβη-ucwf-⇒ ExpSubLamUcwf ImpSubLamUcwf
λExpSubUcwf⇒ = record { ucwf-⇒        = ExpSubUcwf⇒
                      ; lam-preserved = refl~βη
                      ; app-preserved = refl~βη
                      }

ΠExpSubUcwf⇒ : Π-λβη-ucwf-⇒ ExpSubΠUcwf ImpSubΠUcwf
ΠExpSubUcwf⇒ = record { λucwf-⇒     = λExpSubUcwf⇒
                      ; U-preserved = refl~βη
                      ; Π-preserved = refl~βη
                      }

varsExp : ∀ {m n} → Ren m n → Sub-cwf m n
varsExp []      = <>
varsExp (i ∷ ρ) = < varsExp ρ , varExp i >

var-lemma : ∀ {m n} (ρ : Ren m n) → varsExp ρ ∘⋆ p⋆ ≈ varsExp (map suc ρ)
var-lemma []      = left-zero
var-lemma (i ∷ ρ) = begin
  < varsExp ρ , varExp i > ∘⋆ p⋆              ≈⟨ compExt ⟩
  < varsExp ρ ∘⋆ p⋆ , varExp i [ p⋆ ]⋆ >      ≈⟨ cong-<, $ var-lemma ρ ⟩
  < varsExp (map suc ρ) , varExp i [ p⋆ ]⋆ >
  ∎
  where open EqR (SubSetoid {_} {_})

p⋆-norm : ∀ {n} → Sub-cwf (suc n) n
p⋆-norm {n} = varsExp Ren.p

p⋆≈p⋆-norm : ∀ {n} → p⋆ {n} ≈ varsExp (Ren.p)
p⋆≈p⋆-norm {zero}  = emptySub _
p⋆≈p⋆-norm {suc n} = begin
  p⋆                                        ≈⟨ surj-<,> p⋆ ⟩
  < p⋆ ∘⋆ p⋆ , q⋆ [ p⋆ ]⋆ >                 ≈⟨ cong-<, $ cong-∘₁ p⋆≈p⋆-norm ⟩
  < varsExp Ren.p ∘⋆ p⋆ , q⋆ [ p⋆ ]⋆ >      ≈⟨ cong-<, $ var-lemma Ren.p ⟩
  < varsExp (map suc Ren.p) , q⋆ [ p⋆ ]⋆ > 
  ∎
  where open EqR (SubSetoid {_} {_})

↑-var : ∀ {m n} (ρ : Ren m n) → varsExp (Ren.↑ ρ) ≈ < varsExp ρ ∘⋆ p⋆ , q⋆ >
↑-var ρ = cong-<, $ sym≈ $ var-lemma ρ

vars-any : ∀ {m n} (ρ : Ren m n) → ⟪ map var ρ ⟫' ≈ varsExp ρ
vars-any []      = refl≈
vars-any (_ ∷ ρ) = cong-<, $ vars-any ρ 

vars-p : ∀ {n} → ⟪ p {n} ⟫' ≈ varsExp Ren.p
vars-p = vars-any Ren.p

p-preserved : ∀ {n} → ⟪ p {n} ⟫' ≈ p⋆
p-preserved = trans≈ vars-p (sym≈ p⋆≈p⋆-norm)

id-preserved : ∀ {n} → ⟪ id {n} ⟫' ≈ id⋆
id-preserved {zero}  = sym≈ id-zero
id-preserved {suc n} = begin
  < ⟪ p ⟫' , ⟪ q ⟫ > ≈⟨ cong-<, p-preserved ⟩
  < p⋆ , q⋆ >        ≈⟨ sym≈ idExt ⟩
  id⋆
  ∎
  where open EqR (SubSetoid {_} {_})

ren-preserves : ∀ {m n} {ρ : Ren m n} {t} → ⟪ t / ρ ⟫ ~ ⟪ t ⟫ [ varsExp ρ ]⋆
ren-preserves {t = U}                   = sym~ subU
ren-preserves {ρ = []}    {var ()}
ren-preserves {ρ = x ∷ ρ} {var zero}    = sym~ q-sub
ren-preserves {ρ = x ∷ ρ} {var (suc i)} = begin  
  varExp (lookup i ρ)                               ≈⟨ ren-preserves {ρ = ρ} {t = var i} ⟩
  varExp i [ varsExp ρ ]⋆                           ≈⟨ cong-sub₂ (sym≈ p-∘) ⟩
  varExp i [ p⋆ ∘⋆ < varsExp ρ , varExp x > ]⋆      ≈⟨ subComp ⟩ 
  (varExp i [ p⋆ ]⋆) [ < varsExp ρ , varExp x > ]⋆
  ∎
  where open EqR (TmSetoid {_})
ren-preserves {ρ = ρ} {app t u} = begin
  app ⟪ t / ρ ⟫ ⟪ u / ρ ⟫                            ≈⟨ cong-app (ren-preserves {t = t}) (ren-preserves {t = u}) ⟩
  app (⟪ t ⟫ [ varsExp ρ ]⋆) (⟪ u ⟫ [ varsExp ρ ]⋆)  ≈⟨ sym~ subApp ⟩
  (app ⟪ t ⟫ ⟪ u ⟫) [ varsExp ρ ]⋆
  ∎
  where open EqR (TmSetoid {_})
ren-preserves {ρ = ρ} {ƛ t} = begin
  ƛ ⟪ t / Ren.↑ ρ ⟫                           ≈⟨ cong-lam $ ren-preserves {ρ = Ren.↑ ρ} {t = t} ⟩
  ƛ (⟪ t ⟫ [ < varsExp (map suc ρ) , q⋆ > ]⋆) ≈⟨ cong-lam $ cong-sub₂ $ cong-<, $ sym≈ $ var-lemma ρ ⟩
  ƛ (⟪ t ⟫ [ < varsExp ρ ∘⋆ p⋆ , q⋆ > ]⋆)     ≈⟨ sym~ subLam ⟩
  ƛ ⟪ t ⟫ [ varsExp ρ ]⋆
  ∎
  where open EqR (TmSetoid {_})
ren-preserves {ρ = ρ} {Π A B} = begin
  Π ⟪ A / ρ ⟫ ⟪ B / Ren.↑ ρ ⟫                                        ≈⟨ cong-Πl $ ren-preserves {t = A} ⟩
  Π (⟪ A ⟫ [ varsExp ρ ]⋆) ⟪ B / Ren.↑ ρ ⟫                           ≈⟨ cong-Πr $ ren-preserves {ρ = Ren.↑ ρ} {t = B} ⟩
  Π (⟪ A ⟫ [ varsExp ρ ]⋆) (⟪ B ⟫ [ < varsExp (map suc ρ) , q⋆ > ]⋆) ≈⟨ cong-Πr $ cong-sub₂ $ cong-<, $ sym≈ $ var-lemma ρ ⟩
  Π (⟪ A ⟫ [ varsExp ρ ]⋆) (⟪ B ⟫ [ < varsExp ρ ∘⋆ p⋆ , q⋆ > ]⋆)     ≈⟨ sym~ (subΠ {γ = varsExp ρ}) ⟩
  Π ⟪ A ⟫ ⟪ B ⟫ [ varsExp ρ ]⋆
  ∎
  where open EqR (TmSetoid {_})

wk-⟦⟧ : ∀ {n} (t : Tm-cwf n) → ⟦ t [ p⋆ ]⋆ ⟧ ~βη weaken ⟦ t ⟧
wk-⟦⟧ U                               = refl~βη
wk-⟦⟧ q⋆                              = varcong (suc zero)
wk-⟦⟧ (app f t)
  rewrite sym $ wk-sub-p {t = ⟦ f ⟧}
        | sym $ wk-sub-p {t = ⟦ t ⟧}  = refl~βη
wk-⟦⟧ (ƛ t)
  rewrite sym $ /-↑-[] {t = ⟦ t ⟧}    = refl~βη
wk-⟦⟧ (t [ γ ]⋆)
  rewrite sym $ wk-sub-p
            {t = ⟦ t ⟧ [ ⟦ γ ⟧' ]}    = refl~βη
wk-⟦⟧ (Π A B)
  rewrite sym $ wk-sub-p {t = ⟦ A ⟧}
        | sym $ /-↑-[] {t = ⟦ B ⟧}    = refl~βη

wk-⟪⟫ : ∀ {n} (t : Tm-λ n) → ⟪ weaken t ⟫ ~ ⟪ t ⟫ [ p⋆ ]⋆
wk-⟪⟫ U                              = sym~ subU
wk-⟪⟫ (var i) rewrite Ren.lookup-p i = refl~
wk-⟪⟫ (app f t) = begin 
  app ⟪ weaken f ⟫ ⟪ weaken t ⟫       ≈⟨ cong-app (wk-⟪⟫ f) (wk-⟪⟫ t) ⟩
  app (⟪ f ⟫ [ p⋆ ]⋆) (⟪ t ⟫ [ p⋆ ]⋆) ≈⟨ sym~ subApp ⟩
  app ⟪ f ⟫ ⟪ t ⟫ [ p⋆ ]⋆
  ∎
  where open EqR (TmSetoid {_})
wk-⟪⟫ (ƛ t) = begin
  ƛ ⟪ t / Ren.↑ Ren.p ⟫                       ≈⟨ cong-lam $ ren-preserves {ρ = Ren.↑ Ren.p} {t = t} ⟩
  ƛ (⟪ t ⟫ [ varsExp (Ren.↑ Ren.p) ]⋆)        ≈⟨ cong-lam $ cong-sub₂ $ cong-<, $ sym≈ $ var-lemma _ ⟩
  ƛ (⟪ t ⟫ [ < varsExp Ren.p ∘⋆ p⋆ , q⋆ > ]⋆) ≈⟨ cong-lam $ cong-sub₂ $ cong-<, $ cong-∘₁ $ sym≈ p⋆≈p⋆-norm ⟩
  ƛ (⟪ t ⟫ [ < p⋆ ∘⋆ p⋆ , q⋆ > ]⋆)            ≈⟨ sym~ subLam ⟩
  ƛ ⟪ t ⟫ [ p⋆ ]⋆
  ∎
  where open EqR (TmSetoid {_})
wk-⟪⟫ (Π A B) = begin
  Π ⟪ A / Ren.p ⟫ ⟪ B / Ren.↑ Ren.p ⟫                         ≈⟨ cong-Πl $ wk-⟪⟫ A ⟩
  Π (⟪ A ⟫ [ p⋆ ]⋆) ⟪ B / Ren.↑ Ren.p ⟫                       ≈⟨ cong-Πr $ ren-preserves {ρ = Ren.↑ Ren.p} {t = B} ⟩
  Π (⟪ A ⟫ [ p⋆ ]⋆) (⟪ B ⟫ [ varsExp (Ren.↑ Ren.p) ]⋆)        ≈⟨ cong-Πr $ cong-sub₂ $ cong-<, $ sym≈ $ var-lemma _ ⟩
  Π (⟪ A ⟫ [ p⋆ ]⋆) (⟪ B ⟫ [ < varsExp Ren.p ∘⋆ p⋆ , q⋆ > ]⋆) ≈⟨ cong-Πr $ cong-sub₂ $ cong-<, $ cong-∘₁ $ sym≈ p⋆≈p⋆-norm ⟩
  Π (⟪ A ⟫ [ p⋆ ]⋆) (⟪ B ⟫ [ < p⋆ ∘⋆ p⋆ , q⋆ > ]⋆)            ≈⟨ sym~ subΠ  ⟩
  Π ⟪ A ⟫ ⟪ B ⟫ [ p⋆ ]⋆
  ∎
  where open EqR (TmSetoid {_})

map-wk-⟪⟫ : ∀ {m n} (γ : Sub-λ m n) → ⟪ map weaken γ ⟫' ≈ ⟪ γ ⟫' ∘⋆ p⋆
map-wk-⟪⟫ [] = sym≈ left-zero
map-wk-⟪⟫ (t ∷ γ) = begin
  < ⟪ map weaken γ ⟫' , ⟪ weaken t ⟫ > ≈⟨ cong-<, $ map-wk-⟪⟫ γ ⟩
  < ⟪ γ ⟫' ∘⋆ p⋆ , ⟪ weaken t ⟫ >      ≈⟨ cong-,> $ wk-⟪⟫ t ⟩
  < ⟪ γ ⟫' ∘⋆ p⋆ , ⟪ t ⟫ [ p⋆ ]⋆ >     ≈⟨ sym≈ compExt ⟩
  < ⟪ γ ⟫' , ⟪ t ⟫ > ∘⋆ p⋆
  ∎
  where open EqR (SubSetoid {_} {_})

sub-preserved : ∀ {m n} t (γ : Sub-λ m n) → ⟪ t [ γ ] ⟫ ~ ⟪ t ⟫ [ ⟪ γ ⟫' ]⋆
sub-preserved U             _       = sym~ subU
sub-preserved (var zero)    (t ∷ γ) = sym~ q-sub
sub-preserved (var (suc i)) (t ∷ γ) = begin
  ⟪ lookup i γ ⟫                             ≈⟨ sub-preserved (var i) γ ⟩
  ⟪ var i ⟫ [ ⟪ γ ⟫' ]⋆                      ≈⟨ cong-sub₂ $ sym≈ p-∘ ⟩
  ⟪ var i ⟫ [ p⋆ ∘⋆ < ⟪ γ ⟫' , ⟪ t ⟫ > ]⋆    ≈⟨ subComp ⟩
  ⟪ var i ⟫ [ p⋆ ]⋆ [ < ⟪ γ ⟫' , ⟪ t ⟫ > ]⋆
  ∎
  where open EqR (TmSetoid {_})
sub-preserved (app f t) γ = begin
  app ⟪ f [ γ ] ⟫ ⟪ t [ γ ] ⟫                 ≈⟨ cong-app (sub-preserved f γ) (sub-preserved t γ) ⟩
  app (⟪ f ⟫ [ ⟪ γ ⟫' ]⋆) (⟪ t ⟫ [ ⟪ γ ⟫' ]⋆) ≈⟨ sym~ subApp ⟩
  app ⟪ f ⟫ ⟪ t ⟫ [ ⟪ γ ⟫' ]⋆
  ∎
  where open EqR (TmSetoid {_})
sub-preserved (ƛ t) γ = begin
  ƛ ⟪ t [ ↑ γ ] ⟫                           ≈⟨ cong-lam $ sub-preserved t (↑ γ) ⟩
  ƛ (⟪ t ⟫ [ < ⟪ map weaken γ ⟫' , q⋆ > ]⋆) ≈⟨ cong-lam $ cong-sub₂ (cong-<, (map-wk-⟪⟫ γ)) ⟩
  ƛ (⟪ t ⟫ [ < ⟪ γ ⟫' ∘⋆ p⋆ , q⋆ > ]⋆)      ≈⟨ sym~ subLam ⟩
  ƛ ⟪ t ⟫ [ ⟪ γ ⟫' ]⋆
  ∎
  where open EqR (TmSetoid {_})
sub-preserved (Π A B) γ = begin
  Π ⟪ A [ γ ] ⟫ ⟪ B [ ↑ γ ] ⟫                                   ≈⟨ cong-Πl $ sub-preserved A γ ⟩
  Π (⟪ A ⟫ [ ⟪ γ ⟫' ]⋆) ⟪ B [ ↑ γ ] ⟫                           ≈⟨ cong-Πr $ sub-preserved B (↑ γ) ⟩
  Π (⟪ A ⟫ [ ⟪ γ ⟫' ]⋆) (⟪ B ⟫ [ < ⟪ map weaken γ ⟫' , q⋆ > ]⋆) ≈⟨ cong-Πr $ cong-sub₂ $ cong-<, $ map-wk-⟪⟫ γ ⟩
  Π (⟪ A ⟫ [ ⟪ γ ⟫' ]⋆) (⟪ B ⟫ [ < ⟪ γ ⟫' ∘⋆ p⋆ , q⋆ > ]⋆)      ≈⟨ sym~ subΠ ⟩
  Π ⟪ A ⟫ ⟪ B ⟫ [ ⟪ γ ⟫' ]⋆
  ∎
  where open EqR (TmSetoid {_})

∘-preserved : ∀ {m n k} (γ₁ : Sub-λ k n) (γ₂ : Sub-λ m k)
              → ⟪ γ₁ ∘ γ₂ ⟫' ≈ ⟪ γ₁ ⟫' ∘⋆ ⟪ γ₂ ⟫'
∘-preserved []        _ = sym≈ left-zero
∘-preserved (t ∷ γ₁) γ₂ = begin
  < ⟪ γ₁ ∘ γ₂ ⟫' , ⟪ t [ γ₂ ] ⟫ >             ≈⟨ cong-<, $ ∘-preserved γ₁ γ₂ ⟩
  < ⟪ γ₁ ⟫' ∘⋆ ⟪ γ₂ ⟫' , ⟪ t [ γ₂ ] ⟫ >       ≈⟨ cong-,> $ sub-preserved t γ₂ ⟩
  < ⟪ γ₁ ⟫' ∘⋆ ⟪ γ₂ ⟫' , ⟪ t ⟫ [ ⟪ γ₂ ⟫' ]⋆ > ≈⟨ sym≈ compExt ⟩
  < ⟪ γ₁ ⟫' , ⟪ t ⟫ > ∘⋆ ⟪ γ₂ ⟫'
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
                ; <,>-preserved = λ t γ → refl≈
                ; sub-preserved = sub-preserved
                }

λImpSubUcwf⇒ : λβη-ucwf-⇒ ImpSubLamUcwf ExpSubLamUcwf
λImpSubUcwf⇒ = record { ucwf-⇒        = ImpSubUcwf⇒
                      ; lam-preserved = refl~
                      ; app-preserved = refl~
                      }
                      
ΠImpSubUcwf⇒ : Π-λβη-ucwf-⇒ ImpSubΠUcwf ExpSubΠUcwf
ΠImpSubUcwf⇒ = record { λucwf-⇒     = λImpSubUcwf⇒
                      ; U-preserved = refl~
                      ; Π-preserved = refl~
                      }

left-inv-tm : ∀ {n} (t : Tm-cwf n) → ⟪ ⟦ t ⟧ ⟫ ~ t
left-inv-sub : ∀ {m n} (γ : Sub-cwf m n) → ⟪ ⟦ γ ⟧' ⟫' ≈ γ

left-inv-sub id⋆        = id-preserved
left-inv-sub p⋆         = p-preserved
left-inv-sub <>         = refl≈
left-inv-sub < γ , t >  = cong-<,> (left-inv-tm t) (left-inv-sub γ)
left-inv-sub (γ₁ ∘⋆ γ₂) = begin
  ⟪ ⟦ γ₁ ⟧' ∘ ⟦ γ₂ ⟧' ⟫'       ≈⟨ ∘-preserved ⟦ γ₁ ⟧' ⟦ γ₂ ⟧' ⟩
  ⟪ ⟦ γ₁ ⟧' ⟫' ∘⋆ ⟪ ⟦ γ₂ ⟧' ⟫' ≈⟨ cong-∘₁ $ left-inv-sub γ₁ ⟩
  γ₁ ∘⋆ ⟪ ⟦ γ₂ ⟧' ⟫'           ≈⟨ cong-∘₂ $ left-inv-sub γ₂ ⟩
  γ₁ ∘⋆ γ₂
  ∎
  where open EqR (SubSetoid {_} {_})

left-inv-tm U          = refl~
left-inv-tm q⋆         = refl~
left-inv-tm (app f t)  = cong-app (left-inv-tm f) (left-inv-tm t)
left-inv-tm (ƛ t)      = cong-lam $ left-inv-tm t
left-inv-tm (Π A B)    = cong-Π (left-inv-tm A) (left-inv-tm B)
left-inv-tm (t [ γ ]⋆) = begin
  ⟪ ⟦ t ⟧ [ ⟦ γ ⟧' ] ⟫       ≈⟨ sub-preserved ⟦ t ⟧ ⟦ γ ⟧' ⟩
  ⟪ ⟦ t ⟧ ⟫ [ ⟪ ⟦ γ ⟧' ⟫' ]⋆ ≈⟨ cong-sub₁ $ left-inv-tm t ⟩
  t [ ⟪ ⟦ γ ⟧' ⟫' ]⋆         ≈⟨ cong-sub₂ $ left-inv-sub γ ⟩
  t [ γ ]⋆
  ∎
  where open EqR (TmSetoid {_})

right-inv-tm : ∀ {n} (t : Tm-λ n) → ⟦ ⟪ t ⟫ ⟧ ~βη t
right-inv-tm U             = refl~βη
right-inv-tm (app f t)     = apcong (right-inv-tm f) (right-inv-tm t)
right-inv-tm (ƛ t)         = ξ $ right-inv-tm t
right-inv-tm (Π A B)       = Πcong (right-inv-tm A) (right-inv-tm B)
right-inv-tm (var zero)    = refl~βη
right-inv-tm (var (suc i)) = begin
  ⟦ ⟪ var i ⟫ ⟧ [ p ] ≈⟨ congSub-tm $ right-inv-tm (var i) ⟩
  var i [ p ]         ≈⟨ lookup-p~ i ⟩
  var (suc i)
  ∎
  where open EqR (Tm-βη-Setoid {_})

right-inv-sub : ∀ {m n} (γ : Sub-λ m n) → ⟦ ⟪ γ ⟫' ⟧' ≈βη γ
right-inv-sub []      = refl≈βη
right-inv-sub (t ∷ γ) = ext (right-inv-tm t) (right-inv-sub γ)

ExpSubΠUcwf-ImpSubΠUcwf-≅ : Π-λβη-ucwf-≅ ΠExpSubUcwf⇒ ΠImpSubUcwf⇒
ExpSubΠUcwf-ImpSubΠUcwf-≅ = record
                                  { left-inv-tm   = left-inv-tm
                                  ; right-inv-tm  = right-inv-tm
                                  ; left-inv-sub  = left-inv-sub
                                  ; right-inv-sub = right-inv-sub
                                  }
