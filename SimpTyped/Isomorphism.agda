-------------------------------------------------------------------------------
-- The Scwf morphisms between the scwf combinator language and the traditional
-- ST lambda calculus.
-- Proof of the isomoprhism follows
-------------------------------------------------------------------------------
module SimpTyped.Isomorphism where

open import SimpTyped.ScwfComb renaming (Tm to Tm-cwf)
open import SimpTyped.Tm.Syntax
  renaming (Term to Tm-λ ; q to q~ ; weaken to weaken~ ; _[_] to _[_]~
            ; p to p~ ; id to id~ ; cong-[] to cong-[]')
open import SimpTyped.Context
open import SimpTyped.Tm.Properties
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
⟪_⟫ʰ : ∀ {Γ Δ} → Hom Δ Γ → Δ ▹ Γ
⟦_⟧ˢ : ∀ {Γ Δ} → Δ ▹ Γ → Hom Δ Γ

⟦ var ∈Γ ⟧  = varCwf ∈Γ
⟦ t · u ⟧   = app ⟦ t ⟧ ⟦ u ⟧
⟦ ƛ t ⟧     = lam ⟦ t ⟧

⟪ q ⟫       = var here
⟪ t [ ρ ] ⟫ = ⟪ t ⟫ [ ⟪ ρ ⟫ʰ ]~
⟪ lam t ⟫   = ƛ ⟪ t ⟫
⟪ app t u ⟫ = ⟪ t ⟫ · ⟪ u ⟫

⟦_⟧ˢ {ε}     _       = <>
⟦_⟧ˢ {Γ ∙ α} (ρ , t) = < ⟦ ρ ⟧ˢ , ⟦ t ⟧ >

⟪ <> ⟫ʰ        = tt
⟪ id ⟫ʰ        = id~
⟪ p  ⟫ʰ        = p~
⟪ γ ∘ γ' ⟫ʰ    = ⟪ γ ⟫ʰ ⋆ ⟪ γ' ⟫ʰ
⟪ < γ , t > ⟫ʰ = ⟪ γ ⟫ʰ , ⟪ t ⟫

-------------------------------------------------------------------------------
-- Inverse proofs

hom∘▹ : ∀ {Γ Δ} (γ : Hom Γ Δ) → ⟦ ⟪ γ ⟫ʰ ⟧ˢ ~~ γ

λ∘cwf : ∀ {Γ α} (t : Tm-λ Γ α) → ⟪ ⟦ t ⟧ ⟫ ≡ t

cwf∘λ : ∀ {Γ α} (t : Tm-cwf Γ α) → ⟦ ⟪ t ⟫ ⟧ ~ t

▹∘hom : ∀ {Γ Δ} (γ : Γ ▹ Δ) → ⟪ ⟦ γ ⟧ˢ ⟫ʰ ≡ γ

-------------------------------------------------------------------------------
-- supporting properties

p~⟦p⟧ : ∀ {Γ α} → p {Γ} {α} ~~ ⟦ p~ {Γ} ⟧ˢ

[]-comm : ∀ {Γ Δ α} (t : Tm-λ Γ α) (ρ : Δ ▹ Γ) →
           ⟦ t [ ρ ]~ ⟧ ~ ⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]
          
⟦⟧-∘-dist : ∀ {Γ Δ Θ} (ρ : Δ ▹ Θ) (σ : Γ ▹ Δ) →
            ⟦ ρ ⋆ σ ⟧ˢ ~~ ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ

postulate ⟦⟧-∘-distₚ : ∀ {Γ Δ Θ} (ρ : Δ ▹ Θ) (σ : Γ ▹ Δ) → ⟦ ρ ⋆ σ ⟧ˢ ~~ ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ

-- substitution commutes to the other object

[]-comm {ε} (var ()) tt

[]-comm (var here) (ρ , t) = sym~ (q[] ⟦ t ⟧ ⟦ ρ ⟧ˢ)
[]-comm (var (there ∈Γ)) (ρ , t) = begin
  ⟦ tkVar ∈Γ ρ ⟧
    ≈⟨ []-comm (var ∈Γ) ρ ⟩
  ⟦ var ∈Γ ⟧ [ ⟦ ρ ⟧ˢ ]
    ≈⟨ cong-[] refl~ (sym~~ (pCons ⟦ t ⟧ ⟦ ρ ⟧ˢ)) ⟩
  ⟦ var ∈Γ ⟧ [ p ∘ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ]
    ≈⟨ clos ⟦ var ∈Γ ⟧ p < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ⟩
  ⟦ var ∈Γ ⟧ [ p ] [ < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ]
    ∎
  where open EqR (TmCwf {_})
  
[]-comm (t · u) ρ = begin
  app ⟦ t [ ρ ]~ ⟧ ⟦ u [ ρ ]~ ⟧
    ≈⟨ cong-app ([]-comm t ρ) refl~ ⟩
  app (⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]) ⟦ u [ ρ ]~ ⟧
    ≈⟨ cong-app refl~ ([]-comm u ρ) ⟩
  app (⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]) (⟦ u ⟧ [ ⟦ ρ ⟧ˢ ])
    ≈⟨ appCm ⟦ t ⟧ ⟦ u ⟧ ⟦ ρ ⟧ˢ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ [ ⟦ ρ ⟧ˢ ]
    ∎
  where open EqR (TmCwf {_})
  
[]-comm {Γ} (ƛ {α = α} t) ρ = begin
  lam ⟦ t [ ▹-weaken Γ ⊆-∙ ρ , var here ]~ ⟧
    ≈⟨ cong-lam ([]-comm t (▹-weaken Γ ⊆-∙ ρ , var here)) ⟩
  lam (⟦ t ⟧ [ < ⟦ ▹-weaken Γ ⊆-∙ ρ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-[] refl~ (help)) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⋆ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-[] refl~ (cong-<,> refl~ (⟦⟧-∘-distₚ ρ p~))) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⟧ˢ ∘ ⟦ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam (cong-[] refl~ (cong-<,> refl~ (cong-∘ refl~~ (sym~~ p~⟦p⟧)))) ⟩
  lam (⟦ t ⟧ [ < ⟦ ρ ⟧ˢ ∘ p , q > ])
    ≈⟨ sym~ (lamCm ⟦ t ⟧ ⟦ ρ ⟧ˢ) ⟩
  lam ⟦ t ⟧ [ ⟦ ρ ⟧ˢ ]
    ∎
  where open EqR (TmCwf {_})
        help : < ⟦ ▹-weaken Γ (⊆-∙ {a = α}) ρ ⟧ˢ , q > ~~ < ⟦ ρ ⋆ p~ ⟧ˢ , q >
        help rewrite ▹-weaken-⋆-p {Γ} {α = α} ρ = refl~~

-- composition distributes

⟦⟧-∘-dist {Θ = ε} tt σ = sym~~ (∘<> ⟦ σ ⟧ˢ)
⟦⟧-∘-dist {Θ = Θ ∙ x} (ρ , t) σ = begin
  < ⟦ ρ ⋆ σ ⟧ˢ , ⟦ t [ σ ]~ ⟧ >
    ≈⟨ cong-<,> refl~ (⟦⟧-∘-dist ρ σ) ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t [ σ ]~ ⟧ >
    ≈⟨ cong-<,> ([]-comm t σ) refl~~ ⟩
  < ⟦ ρ ⟧ˢ ∘ ⟦ σ ⟧ˢ , ⟦ t ⟧ [ ⟦ σ ⟧ˢ ] >
    ≈⟨ sym~~ (maps ⟦ t ⟧ ⟦ ρ ⟧ˢ ⟦ σ ⟧ˢ) ⟩
  < ⟦ ρ ⟧ˢ , ⟦ t ⟧ > ∘ ⟦ σ ⟧ˢ
    ∎
  where open EqR (HmSetoid {_} {_})

-- inverse lambda term

λ∘cwf (var here) = refl
λ∘cwf (t · u) = cong₂ _·_ (λ∘cwf t) (λ∘cwf u)
λ∘cwf (ƛ t) = cong ƛ (λ∘cwf t)
λ∘cwf {α = α} (var (there ∈Γ)) = begin
  ⟪ ⟦ var ∈Γ ⟧ ⟫ [ p~ ]~
    ≡⟨ cong (_[ p~ ]~) (λ∘cwf (var ∈Γ)) ⟩
  var ∈Γ [ p~ ]~
    ≡⟨ sub-p (var ∈Γ) ⟩
  weaken~ ⊆-∙ (var ∈Γ)
    ≡⟨⟩
  var (there (sub-in ⊆-refl ∈Γ))
    ≡⟨ cong (var F.∘ there) (sub-in-refl ∈Γ) ⟩
  var (there ∈Γ)
    ∎
  where open P.≡-Reasoning

-- inverse explicit term

cwf∘λ q = refl~
cwf∘λ (lam t) = cong-lam (cwf∘λ t)
cwf∘λ (app t u) = cong-app (cwf∘λ t) (cwf∘λ u)
cwf∘λ (t [ γ ]) = begin
  ⟦ ⟪ t ⟫ [ ⟪ γ ⟫ʰ ]~ ⟧
    ≈⟨ []-comm ⟪ t ⟫ ⟪ γ ⟫ʰ ⟩
  ⟦ ⟪ t ⟫ ⟧ [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ]
    ≈⟨ cong-[] (cwf∘λ t) refl~~ ⟩
  t [ ⟦ ⟪ γ ⟫ʰ ⟧ˢ ]
    ≈⟨ cong-[] refl~ (hom∘▹ γ) ⟩
  t [ γ ]
    ∎
  where open EqR (TmCwf {_})

-- empty sub case

hom∘▹ <> = refl~~

-- identity case

hom∘▹ (id {ε}) = sym~~ (homε~<> id)
hom∘▹ (id {Γ ∙ α}) = sym~~ $ begin
  id
    ≈⟨ varp ⟩
  < p , q >
    ≈⟨ cong-<,> refl~ (sym~~ (hom∘▹ p)) ⟩
  < ⟦ p~ ⟧ˢ , q >
    ∎
  where open EqR (HmSetoid {_} {_})

-- projection case

hom∘▹ p = sym~~ p~⟦p⟧

-- composition case

hom∘▹ (γ ∘ γ') = begin
  ⟦ ⟪ γ ⟫ʰ ⋆ ⟪ γ' ⟫ʰ ⟧ˢ
    ≈⟨ ⟦⟧-∘-dist ⟪ γ ⟫ʰ ⟪ γ' ⟫ʰ ⟩
  ⟦ ⟪ γ ⟫ʰ ⟧ˢ ∘ ⟦ ⟪ γ' ⟫ʰ ⟧ˢ
    ≈⟨ cong-∘ (hom∘▹ γ) refl~~ ⟩
  γ ∘ ⟦ ⟪ γ' ⟫ʰ ⟧ˢ
    ≈⟨ cong-∘ refl~~ (hom∘▹ γ') ⟩
  γ ∘ γ'
    ∎
  where open EqR (HmSetoid {_} {_})

-- cons case

hom∘▹ < γ , t > = cong-<,> (cwf∘λ t) (hom∘▹ γ)

-- inverse for concrete substitution

▹∘hom {Δ = ε} tt = refl
▹∘hom {Δ = Δ ∙ x} (γ , t) = cong₂ _,_ (▹∘hom γ) (λ∘cwf t)

-------------------------------------------------------------------------------
-- projection proof

vars : ∀ {Γ Δ} → Δ ▸ Γ → Hom Δ Γ
vars {ε}     tt      = <>
vars {Γ ∙ x} (ρ , t) = < vars ρ , varCwf t >

▸-to-hom : ∀ {Δ Γ} (f : ∀ {α} → α ∈ Δ → Tm-cwf Δ α) → Δ ▸ Γ → Hom Δ Γ
▸-to-hom {Γ = ε}     _ tt      = <>
▸-to-hom {Γ = Γ ∙ x} f (ρ , t) = < ▸-to-hom f ρ , f t >

map~mapcwf : ∀ {Γ Δ} (ρ : Δ ▸ Γ) →
              ⟦ ▸-to-▹ var ρ ⟧ˢ ~~ ▸-to-hom varCwf ρ
map~mapcwf {ε}     tt      = refl~~
map~mapcwf {Γ ∙ x} (ρ , _) = cong-<,> refl~ (map~mapcwf ρ)

pCwf : ∀ {Γ α} → Hom (Γ ∙ α) Γ
pCwf = ▸-to-hom varCwf pV

vars~hom : ∀ {Γ Δ} (ρ : Δ ▸ Γ) → vars ρ ~~ ▸-to-hom varCwf ρ
vars~hom {ε}     tt      = refl~~
vars~hom {Γ ∙ x} (ρ , t) = cong-<,> refl~ (vars~hom ρ)

var-lemma : ∀ {Γ Δ α} (ρ : Δ ▸ Γ) →
             vars ρ ∘ (p {α = α}) ~~ vars (map-∈ there ρ)
var-lemma {ε} tt = ∘<> p
var-lemma {Γ ∙ x} (ρ , t) = begin
  < vars ρ , varCwf t > ∘ p
    ≈⟨ maps (varCwf t) (vars ρ) p ⟩
  < vars ρ ∘ p , varCwf t [ p ] >
    ≈⟨ cong-<,> refl~ (var-lemma ρ) ⟩
  <  vars (map-∈ there ρ) , varCwf t [ p ] >
    ∎
  where open EqR (HmSetoid {_} {_})

help : ∀ {Γ x α} →
        vars (map-∈ {α = x} (there) (map-∈ {α = α} (there) idV)) ~~
        vars (map-∈ (there) (▸-weaken Γ (step ⊆-refl) idV))
help {Γ} {x} {α} rewrite mapwk {Γ} {α = x} {α} idV = refl~~

p~vars : ∀ {Γ α} → p {α = α} ~~ vars (pV {Γ} {α})
p~vars {ε} = homε~<> p
p~vars {Γ ∙ x} {α} = let (ρ , t) = (pV {Γ ∙ x})
                     in  begin
  p
    ≈⟨ surj-<,> p ⟩
  < p ∘ p , q [ p ] >
    ≈⟨ cong-<,> refl~ (cong-∘ p~vars refl~~) ⟩
  < vars pV ∘ p , q [ p ] >
    ≈⟨ cong-<,> refl~ (var-lemma pV) ⟩
  < vars (map-∈ there pV) , q [ p ] >
    ≈⟨ cong-<,> refl~ help ⟩
  < vars ρ , q [ p ] >
    ∎
  where open EqR (HmSetoid {_} {_})

p~⟦p⟧ {Γ} {α} =
  trans~~ p~vars (trans~~ (vars~hom _)
    (trans~~ (sym~~ (map~mapcwf _)) g))
  where g : ⟦ ▸-to-▹ var (pV {Γ} {α}) ⟧ˢ ~~ ⟦ p~ ⟧ˢ
        g rewrite pIsVarP {Γ} {α} = refl~~
