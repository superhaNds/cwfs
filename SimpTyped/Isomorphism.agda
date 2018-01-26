-------------------------------------------------------------------------------
-- The Scwf morphisms between the scwf combinator language and the traditional
-- ST lambda calculus.
-- Proof of the isomoprhism follows
-------------------------------------------------------------------------------
module SimpTyped.Isomorphism where

open import SimpTyped.ScwfComb renaming (Tm to Tm-cwf ; Sub to Sub-cwf)
open import SimpTyped.Tm.Syntax
  renaming (Tm to Tm-λ ; Sub to Sub-λ ; _∘_ to _∘λ_ ; q to q-λ ; weaken to weaken-λ ; _[_] to _[_]λ
            ; p to p-λ ; id to id-λ ; cong-sub to cong-sub-λ) hiding (cong-∘)
open import SimpTyped.Context
open import SimpTyped.Tm.Properties hiding (id₀)
open import SimpTyped.Context
open import SimpTyped.Type
open import Function as F using (_$_ ; flip)
open import Relation.Binary.PropositionalEquality as P hiding ([_] ; cong-app)
open import Data.Product using (_,_)
open import Data.List hiding ([_])
open import Data.Unit using (⊤ ; tt)
import Relation.Binary.EqReasoning as EqR

-------------------------------------------------------------------------------
-- Translation functions between the scwfs

-- Creates a variable for the explicit language using weakenings on q

varCwf : ∀ {Γ α} (φ : α ∈ Γ) → Tm-cwf Γ α
varCwf here      = q
varCwf (there φ) = varCwf φ [ p ]

⟦_⟧  : ∀ {Γ α} → Tm-λ Γ α → Tm-cwf Γ α
⟪_⟫  : ∀ {Γ α} → Tm-cwf Γ α → Tm-λ Γ α
⟪_⟫ʰ : ∀ {Γ Δ} → Sub-cwf Δ Γ → Sub-λ Δ Γ
⟦_⟧ˢ : ∀ {Γ Δ} → Sub-λ Δ Γ → Sub-cwf Δ Γ

⟦ var ∈Γ ⟧  = varCwf ∈Γ
⟦ t · u ⟧   = app ⟦ t ⟧ ⟦ u ⟧
⟦ ƛ t ⟧     = lam ⟦ t ⟧

⟪ q ⟫       = q-λ
⟪ t [ ρ ] ⟫ = ⟪ t ⟫ [ ⟪ ρ ⟫ʰ ]λ
⟪ lam t ⟫   = ƛ ⟪ t ⟫
⟪ app t u ⟫ = ⟪ t ⟫ · ⟪ u ⟫

⟦_⟧ˢ {ε}     _       = <>
⟦_⟧ˢ {Γ ∙ α} (ρ , t) = < ⟦ ρ ⟧ˢ , ⟦ t ⟧ >

⟪ <> ⟫ʰ        = tt
⟪ id ⟫ʰ        = id-λ
⟪ p  ⟫ʰ        = p-λ
⟪ γ ∘ γ' ⟫ʰ    = ⟪ γ ⟫ʰ ∘λ ⟪ γ' ⟫ʰ
⟪ < γ , t > ⟫ʰ = ⟪ γ ⟫ʰ , ⟪ t ⟫

-------------------------------------------------------------------------------
-- Inverse proofs

sub-cwf⇒λ : ∀ {Γ Δ} (γ : Sub-cwf Γ Δ) → ⟦ ⟪ γ ⟫ʰ ⟧ˢ ≋ γ

tm-λ⇒cwf : ∀ {Γ α} (t : Tm-λ Γ α) → ⟪ ⟦ t ⟧ ⟫ ≡ t

tm-cwf⇒λ : ∀ {Γ α} (t : Tm-cwf Γ α) → ⟦ ⟪ t ⟫ ⟧ ≈ t

sub-λ⇒cwf : ∀ {Γ Δ} (γ : Sub-λ Γ Δ) → ⟪ ⟦ γ ⟧ˢ ⟫ʰ ≡ γ

-------------------------------------------------------------------------------
-- supporting properties

p~⟦p⟧ : ∀ {Γ α} → p {Γ} {α} ≋ ⟦ p-λ {Γ} ⟧ˢ

[]-comm : ∀ {Γ Δ α} (t : Tm-λ Γ α) (ρ : Sub-λ Δ Γ) →
           ⟦ t [ ρ ]λ ⟧ ≈ ⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]
          
⟦⟧-∘-dist : ∀ {Γ Δ Θ} (ρ : Sub-λ Δ Θ) (σ : Sub-λ Γ Δ) →
            ⟦ ρ ∘λ σ ⟧ˢ ≋ ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ

postulate ⟦⟧-∘-distₚ : ∀ {Γ Δ Θ} (ρ : Sub-λ Δ Θ) (σ : Sub-λ Γ Δ) → ⟦ ρ ∘λ σ ⟧ˢ ≋ ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ

-- substitution commutes to the other object

[]-comm {ε} (var ()) tt

[]-comm (var here) (ρ , t) = sym≈ (qCons ⟦ t ⟧ ⟦ ρ ⟧ˢ)
[]-comm (var (there ∈Γ)) (ρ , t) = begin
  ⟦ tkVar ∈Γ ρ ⟧
    ≈⟨ []-comm (var ∈Γ) ρ ⟩
  ⟦ var ∈Γ ⟧ [ ⟦ ρ ⟧ˢ ]
    ≈⟨ cong-sub refl≈ (sym≋ (pCons ⟦ t ⟧ ⟦ ρ ⟧ˢ)) ⟩
  ⟦ var ∈Γ ⟧ [ p ∘ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ]
    ≈⟨ subComp ⟦ var ∈Γ ⟧ p < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ⟩
  ⟦ var ∈Γ ⟧ [ p ] [ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ]
    ∎
  where open EqR (TmCwf {_})
  
[]-comm (t · u) ρ = begin
  app ⟦ t [ ρ ]λ ⟧ ⟦ u [ ρ ]λ ⟧
    ≈⟨ cong-app ([]-comm t ρ) refl≈ ⟩
  app (⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]) ⟦ u [ ρ ]λ ⟧
    ≈⟨ cong-app refl≈ ([]-comm u ρ) ⟩
  app (⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]) (⟦ u ⟧ [ ⟦ ρ ⟧ˢ ])
    ≈⟨ subApp ⟦ t ⟧ ⟦ u ⟧ ⟦ ρ ⟧ˢ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ [ ⟦ ρ ⟧ˢ ]
    ∎
  where open EqR (TmCwf {_})
  
[]-comm {Γ} (ƛ {α = α} t) ρ = begin
  lam ⟦ t [ wk-sub Γ ⊆-∙ ρ , var here ]λ ⟧
    ≈⟨ cong-lam ([]-comm t (wk-sub Γ ⊆-∙ ρ , var here)) ⟩
  lam (⟦ t ⟧ [ < ⟦ wk-sub Γ ⊆-∙ ρ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-sub refl≈ (help)) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ∘λ p-λ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-sub refl≈ (cong-<,> refl≈ (⟦⟧-∘-distₚ ρ p-λ))) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⟧ˢ ∘ ⟦ p-λ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-sub refl≈ (cong-<,> refl≈ (cong-∘ refl≋ (sym≋ p~⟦p⟧)))) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⟧ˢ ∘ p , q > ])
    ≈⟨ sym≈ (subLam ⟦ t ⟧ ⟦ ρ ⟧ˢ) ⟩
  lam ⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]
    ∎
  where open EqR (TmCwf {_})
        help : < ⟦ wk-sub Γ (⊆-∙ {a = α}) ρ ⟧ˢ , q > ≋ < ⟦ ρ ∘λ p-λ ⟧ˢ , q >
        help rewrite wk-sub-∘-p {Γ} {α = α} ρ = refl≋

-- composition distributes

⟦⟧-∘-dist {Θ = ε} tt σ = sym≋ (<>Lzero ⟦ σ ⟧ˢ)
⟦⟧-∘-dist {Θ = Θ ∙ x} (ρ , t) σ = begin
  < ⟦ ρ ∘λ σ ⟧ˢ , ⟦ t [ σ ]λ ⟧ >
    ≈⟨ cong-<,> refl≈ (⟦⟧-∘-dist ρ σ) ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t [ σ ]λ ⟧ >
    ≈⟨ cong-<,> ([]-comm t σ) refl≋ ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t ⟧ [ ⟦ σ ⟧ˢ ] >
    ≈⟨ sym≋ (compExt ⟦ t ⟧ ⟦ ρ ⟧ˢ ⟦ σ ⟧ˢ) ⟩
  < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ∘ ⟦ σ ⟧ˢ
    ∎
  where open EqR (HmSetoid {_} {_})

-- inverse lambda term

tm-λ⇒cwf (var here) = refl
tm-λ⇒cwf (t · u) = cong₂ _·_ (tm-λ⇒cwf t) (tm-λ⇒cwf u)
tm-λ⇒cwf (ƛ t) = cong ƛ (tm-λ⇒cwf t)
tm-λ⇒cwf {α = α} (var (there ∈Γ)) = begin
  ⟪ ⟦ var ∈Γ ⟧ ⟫ [ p-λ ]λ
    ≡⟨ cong (_[ p-λ ]λ) (tm-λ⇒cwf (var ∈Γ)) ⟩
  var ∈Γ [ p-λ ]λ
    ≡⟨ sub-p (var ∈Γ) ⟩
  weaken-λ ⊆-∙ (var ∈Γ)
    ≡⟨⟩
  var (there (sub-in ⊆-refl ∈Γ))
    ≡⟨ cong (var F.∘ there) (sub-in-refl ∈Γ) ⟩
  var (there ∈Γ)
    ∎
  where open P.≡-Reasoning

-- inverse explicit term

tm-cwf⇒λ q = refl≈
tm-cwf⇒λ (lam t) = cong-lam (tm-cwf⇒λ t)
tm-cwf⇒λ (app t u) = cong-app (tm-cwf⇒λ t) (tm-cwf⇒λ u)
tm-cwf⇒λ (t [ γ ]) = begin
  ⟦ ⟪ t ⟫ [ ⟪ γ ⟫ʰ ]λ ⟧
    ≈⟨ []-comm ⟪ t ⟫ ⟪ γ ⟫ʰ ⟩
  ⟦ ⟪ t ⟫ ⟧ [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ]
    ≈⟨ cong-sub (tm-cwf⇒λ t) refl≋ ⟩
  t [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ]
    ≈⟨ cong-sub refl≈ (sub-cwf⇒λ γ) ⟩
  t [ γ ]
    ∎
  where open EqR (TmCwf {_})

-- empty sub case

sub-cwf⇒λ <> = refl≋

-- identity case

sub-cwf⇒λ (id {ε}) = sym≋ id₀
sub-cwf⇒λ (id {Γ ∙ α}) = sym≋ $ begin
  id
    ≈⟨ idExt ⟩
  < p , q >
    ≈⟨ cong-<,> refl≈ (sym≋ (sub-cwf⇒λ p)) ⟩
  < ⟦ p-λ ⟧ˢ , q >
    ∎
  where open EqR (HmSetoid {_} {_})

-- projection case

sub-cwf⇒λ p = sym≋ p~⟦p⟧

-- composition case

sub-cwf⇒λ (γ ∘ γ') = begin
  ⟦ ⟪ γ ⟫ʰ ∘λ ⟪ γ' ⟫ʰ ⟧ˢ
    ≈⟨ ⟦⟧-∘-dist ⟪ γ ⟫ʰ ⟪ γ' ⟫ʰ ⟩
  ⟦ ⟪ γ ⟫ʰ ⟧ˢ ∘ ⟦ ⟪ γ' ⟫ʰ ⟧ˢ
    ≈⟨ cong-∘ (sub-cwf⇒λ γ) refl≋ ⟩
  γ ∘ ⟦ ⟪ γ' ⟫ʰ ⟧ˢ
    ≈⟨ cong-∘ refl≋ (sub-cwf⇒λ γ') ⟩
  γ ∘ γ'
    ∎
  where open EqR (HmSetoid {_} {_})

-- cons case

sub-cwf⇒λ < γ , t > = cong-<,> (tm-cwf⇒λ t) (sub-cwf⇒λ γ)

-- inverse for concrete substitution

sub-λ⇒cwf {Δ = ε} tt = refl
sub-λ⇒cwf {Δ = Δ ∙ x} (γ , t) = cong₂ _,_ (sub-λ⇒cwf γ) (tm-λ⇒cwf t)

-------------------------------------------------------------------------------
-- projection proof

vars : ∀ {Γ Δ} → Δ ▸ Γ → Sub-cwf Δ Γ
vars {ε}     tt      = <>
vars {Γ ∙ x} (ρ , t) = < vars ρ , varCwf t >

▸-to-hom : ∀ {Δ Γ} (f : ∀ {α} → α ∈ Δ → Tm-cwf Δ α) → Δ ▸ Γ → Sub-cwf Δ Γ
▸-to-hom {Γ = ε}     _ tt      = <>
▸-to-hom {Γ = Γ ∙ x} f (ρ , t) = < ▸-to-hom f ρ , f t >

map≈mapcwf : ∀ {Γ Δ} (ρ : Δ ▸ Γ) →
              ⟦ ▸-to-▹ var ρ ⟧ˢ ≋ ▸-to-hom varCwf ρ
map≈mapcwf {ε}     tt      = refl≋
map≈mapcwf {Γ ∙ x} (ρ , _) = cong-<,> refl≈ (map≈mapcwf ρ)

pCwf : ∀ {Γ α} → Sub-cwf (Γ ∙ α) Γ
pCwf = ▸-to-hom varCwf pV

vars≈hom : ∀ {Γ Δ} (ρ : Δ ▸ Γ) → vars ρ ≋ ▸-to-hom varCwf ρ
vars≈hom {ε}     tt      = refl≋
vars≈hom {Γ ∙ x} (ρ , t) = cong-<,> refl≈ (vars≈hom ρ)

var-lemma : ∀ {Γ Δ α} (ρ : Δ ▸ Γ) →
             vars ρ ∘ (p {α = α}) ≋ vars (map-∈ there ρ)
var-lemma {ε} tt = <>Lzero p
var-lemma {Γ ∙ x} (ρ , t) = begin
  < vars ρ , varCwf t > ∘ p
    ≈⟨ compExt (varCwf t) (vars ρ) p ⟩
  < vars ρ ∘ p , varCwf t [ p ] >
    ≈⟨ cong-<,> refl≈ (var-lemma ρ) ⟩
  <  vars (map-∈ there ρ) , varCwf t [ p ] >
    ∎
  where open EqR (HmSetoid {_} {_})

help : ∀ {Γ x α} →
        vars (map-∈ {α = x} (there) (map-∈ {α = α} (there) idV)) ≋
        vars (map-∈ (there) (▸-weaken Γ (step ⊆-refl) idV))
help {Γ} {x} {α} rewrite mapwk {Γ} {α = x} {α} idV = refl≋

p≈vars : ∀ {Γ α} → p {α = α} ≋ vars (pV {Γ} {α})
p≈vars {ε} = ter-arrow p
p≈vars {Γ ∙ x} {α} = let (ρ , t) = (pV {Γ ∙ x})
                     in  begin
  p
    ≈⟨ surj-<,> p ⟩
  < p ∘ p , q [ p ] >
    ≈⟨ cong-<,> refl≈ (cong-∘ p≈vars refl≋) ⟩
  < vars pV ∘ p , q [ p ] >
    ≈⟨ cong-<,> refl≈ (var-lemma pV) ⟩
  < vars (map-∈ there pV) , q [ p ] >
    ≈⟨ cong-<,> refl≈ help ⟩
  < vars ρ , q [ p ] >
    ∎
  where open EqR (HmSetoid {_} {_})

p~⟦p⟧ {Γ} {α} =
  trans≋ p≈vars (trans≋ (vars≈hom _)
    (trans≋ (sym≋ (map≈mapcwf _)) g))
  where g : ⟦ ▸-to-▹ var (pV {Γ} {α}) ⟧ˢ ≋ ⟦ p-λ ⟧ˢ
        g rewrite pIsVarP {Γ} {α} = refl≋
