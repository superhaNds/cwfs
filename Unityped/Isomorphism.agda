---------------------------------------------------------------------------------------------------
-- Contains the definitions of the bijections between the setoids of wellscoped terms and terms as
-- a Ucwf. Moreover, a proof that they are inverses of each other, which means the objects
-- are isomorphic in the category of cwfs.
---------------------------------------------------------------------------------------------------

module Unityped.Isomorphism where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_$_ ; flip)
open import Unityped.UcwfModel renaming (Term to Tm-cwf)
open import Unityped.Wellscoped
  renaming (Term to Tm-λ ; p to p~ ; _[_] to _[_]~ ; id to id~ ; weaken to weaken~ ; q to q~)
  hiding (maps)
open import Unityped.Projection
open import Unityped.Wellscoped.Properties  
open import Relation.Binary.PropositionalEquality hiding ([_] ; cong-app)
import Relation.Binary.EqReasoning as EqR

---------------------------------------------------------------------------------------------------
-- The bijection between wellscoped λ terms and terms as a Ucwf

-- The translation functions (morphisms)

⟦_⟧  : ∀ {n} → Tm-λ n → Tm-cwf n
⟦_⟧ˢ : ∀ {m n} → Subst m n → Hom m n
⟪_⟫  : ∀ {n} → Tm-cwf n → Tm-λ n
⟪_⟫ʰ : ∀ {m n} → Hom m n → Subst m n

-- Substitutions as vectors to a Hom

⟦ [] ⟧ˢ    = <>
⟦ t ∷ σ ⟧ˢ = < ⟦ σ ⟧ˢ , ⟦ t ⟧ > 

-- Traditional lambda calculus terms to Ucwf terms

⟦ var i ⟧ = PProof.varCwf i
⟦ ƛ t ⟧   = lam ⟦ t ⟧
⟦ t · u ⟧ = app ⟦ t ⟧ ⟦ u ⟧

-- Ucwf terms to lambda terms, (substitution is a constructor which is mapped to the meta operation)

⟪ q ⟫        = var zero
⟪ t [ us ] ⟫ = ⟪ t ⟫ [ ⟪ us ⟫ʰ ]~
⟪ lam t ⟫    = ƛ ⟪ t ⟫
⟪ app t u ⟫  = ⟪ t ⟫ · ⟪ u ⟫

-- Homs to vector substitutions

⟪ id ⟫ʰ         = id~
⟪ ts ∘ us ⟫ʰ    = ⟪ ts ⟫ʰ ⋆ ⟪ us ⟫ʰ
⟪ p ⟫ʰ          = p~
⟪ <> ⟫ʰ         = []
⟪ < ts , t > ⟫ʰ = ⟪ ts ⟫ʰ ∙ ⟪ t ⟫

---------------------------------------------------------------------------------------------------
-- Proofs that the translation functions are inverses of each other

-- Auxiliary props

lemmaₚ : ∀ n → PProof.pNorm n ~~ ⟦ p~ ⟧ˢ
  
p~⟦p⟧ : ∀ {n} → p ~~ ⟦ p~ ⟧ˢ
p~⟦p⟧ {n} = sym~~ $ trans~~ (sym~~ $ lemmaₚ n)
                            (sym~~ $ PProof.p~vars n)

-- Interpreting a composition distributes

postulate ⟦⟧-∘-distₚ : ∀ {m n k} (σ : Subst n k) (γ : Subst m n) → ⟦ σ ⋆ γ ⟧ˢ ~~ ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ

⟦⟧-∘-dist : ∀ {m n k} (σ : Subst n k) (γ : Subst m n) → ⟦ σ ⋆ γ ⟧ˢ ~~ ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ

-- Interpreting a substitution commutes

[]-comm : ∀ {m n} (t : Tm-λ n) (σ : Subst m n) → ⟦ t [ σ ]~ ⟧ ~ ⟦ t ⟧ [ ⟦ σ ⟧ˢ ]

[]-comm (var zero)    (x ∷ σ) = qCons ⟦ x ⟧ ⟦ σ ⟧ˢ
[]-comm (var (suc ι)) (x ∷ σ) = sym~ $ begin
  ⟦ var ι ⟧ [ p ] [ < ⟦ σ ⟧ˢ , ⟦ x ⟧ > ]
    ≈⟨ sym~ (clos ⟦ var ι ⟧ p < ⟦ σ ⟧ˢ , ⟦ x ⟧ >) ⟩
  ⟦ var ι ⟧ [ p ∘ < ⟦ σ ⟧ˢ , ⟦ x ⟧ > ]
    ≈⟨ sym~ (cong-[] refl~ (pCons ⟦ x ⟧ ⟦ σ ⟧ˢ)) ⟩
  ⟦ var ι ⟧ [ ⟦ σ ⟧ˢ ]
    ≈⟨ sym~ ([]-comm (var ι) σ) ⟩
  ⟦ lookup ι σ ⟧
    ∎
  where open EqR (TermS {_})

[]-comm (t · u) σ = begin
  app ⟦ t [ σ ]~ ⟧ ⟦ u [ σ ]~ ⟧
    ≈⟨ cong-app ([]-comm t σ) refl~ ⟩
  app (⟦ t ⟧ [ ⟦ σ ⟧ˢ ]) (⟦ u [ σ ]~ ⟧)
    ≈⟨ cong-app refl~ ([]-comm u σ) ⟩
  app (⟦ t ⟧ [ ⟦ σ ⟧ˢ ]) (⟦ u ⟧ [ ⟦ σ ⟧ˢ ])
    ≈⟨ appCm ⟦ t ⟧ ⟦ u ⟧ ⟦ σ ⟧ˢ ⟩
  app ⟦ t ⟧ ⟦ u ⟧ [ ⟦ σ ⟧ˢ ]
    ∎
  where open EqR (TermS {_})

[]-comm (ƛ t) σ = begin
  lam ⟦ t [ ↑ₛ σ ]~ ⟧
    ≈⟨ cong-lam $ []-comm t (↑ₛ σ) ⟩
  lam (⟦ t ⟧ [ < ⟦ map weaken~ σ ⟧ˢ , q > ])
    ≈⟨ cong-lam $ cong-[] refl~ help ⟩
  lam (⟦ t ⟧ [ < ⟦ σ ⋆ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam $ cong-[] refl~ (cong-<,> refl~ (⟦⟧-∘-distₚ σ p~)) ⟩ 
  lam (⟦ t ⟧ [ < ⟦ σ ⟧ˢ ∘ ⟦ p~ ⟧ˢ , q > ])
    ≈⟨ cong-lam $ cong-[] refl~ (cong-<,> refl~ (cong-∘ refl~~ (sym~~ $ p~⟦p⟧))) ⟩ 
  lam (⟦ t ⟧ [ < ⟦ σ ⟧ˢ ∘ p , q > ])
    ≈⟨ sym~ (lamCm ⟦ t ⟧ ⟦ σ ⟧ˢ) ⟩
  lam ⟦ t ⟧ [ ⟦ σ ⟧ˢ ]
    ∎
  where open EqR (TermS {_})
        help : < ⟦ map weaken~ σ ⟧ˢ , q > ~~ < ⟦ σ ⋆ p~ ⟧ˢ , q >
        help rewrite sym (mapWk-⋆p σ) = refl~~

⟦⟧-∘-dist [] γ = sym~~ (∘<> ⟦ γ ⟧ˢ)
⟦⟧-∘-dist (t ∷ σ) γ = begin
  < ⟦ σ ⋆ γ ⟧ˢ , ⟦ t [ γ ]~ ⟧ >
    ≈⟨ cong-<,> refl~ (⟦⟧-∘-dist σ γ) ⟩ 
  < ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ , ⟦ t [ γ ]~ ⟧ >
    ≈⟨ cong-<,> ([]-comm t γ) refl~~ ⟩
  < ⟦ σ ⟧ˢ ∘ ⟦ γ ⟧ˢ , ⟦ t ⟧ [ ⟦ γ ⟧ˢ ] >
    ≈⟨ sym~~ (maps ⟦ t ⟧ ⟦ σ ⟧ˢ ⟦ γ ⟧ˢ) ⟩
  < ⟦ σ ⟧ˢ , ⟦ t ⟧ > ∘ ⟦ γ ⟧ˢ
    ∎
  where open EqR (HomS {_} {_})
  
---------------------------------------------------------------------------------------------------
-- Inverses

-- A scope safe term mapped to the cwf world returns the same

ws∘cwf : ∀ {n} (t : Tm-λ n) → t ≡ ⟪ ⟦ t ⟧ ⟫

-- A cwf term mapped to a scope safe term returns the same

cwf∘ws : ∀ {n} (t : Tm-cwf n) → t ~ ⟦ ⟪ t ⟫ ⟧

-- A Hom mapped to a vector substitution returns the same

hom∘sub : ∀ {m n} (h : Hom m n) → h ~~ ⟦ ⟪ h ⟫ʰ ⟧ˢ

-- A vector substitution mapped to a hom returns the same

sub∘hom : ∀ {m n} (ρ : Subst m n) → ρ ≡ ⟪ ⟦ ρ ⟧ˢ ⟫ʰ

-- t ∈ Tm-λ n ⇒ ⟪ ⟦ t ⟧ ⟫ ≡ t
 
ws∘cwf (ƛ t) = cong-ƛ (ws∘cwf t)
ws∘cwf (t · u) = cong-ap (ws∘cwf t) (ws∘cwf u)
ws∘cwf (var zero) = refl
ws∘cwf (var (suc i))
  rewrite sym $ lookup-p i
    = cong (_[ p~ ]~) (ws∘cwf (var i))

-- t ∈ Tm-cwf n ⇒ ⟦ ⟪ t ⟫ ⟧ ~ t

cwf∘ws q = refl~
cwf∘ws (lam t) = cong-lam (cwf∘ws t) 
cwf∘ws (app t u) = cong-app (cwf∘ws t) (cwf∘ws u)
cwf∘ws (t [ us ]) = sym~ $ begin
  ⟦ ⟪ t ⟫ [ ⟪ us ⟫ʰ ]~ ⟧      ≈⟨ []-comm ⟪ t ⟫ ⟪ us ⟫ʰ ⟩
  ⟦ ⟪ t ⟫ ⟧ [ ⟦ ⟪ us ⟫ʰ ⟧ˢ ]  ≈⟨ sym~ (cong-[] (cwf∘ws t) refl~~) ⟩
  t [ ⟦ ⟪ us ⟫ʰ ⟧ˢ ]          ≈⟨ sym~ (cong-[] refl~ (hom∘sub us)) ⟩
  t [ us ]                    ∎
  where open EqR (TermS {_})

-- h ∈ Hom m n ⇒ ⟦ ⟪ h ⟫ ⟧ ~ h

hom∘sub (id {zero}) = id₀
hom∘sub (id {suc m}) = begin
  id {1 + m}                ≈⟨ varp ⟩
  < p , q >                 ≈⟨ cong-<,> refl~ (hom∘sub p) ⟩ 
  < ⟦ p~ ⟧ˢ , q >           ∎
  where open EqR (HomS {_} {_})

hom∘sub (γ ∘ δ) = sym~~ $ begin
  ⟦ ⟪ γ ⟫ʰ ⋆ ⟪ δ ⟫ʰ ⟧ˢ
    ≈⟨ ⟦⟧-∘-dist ⟪ γ ⟫ʰ ⟪ δ ⟫ʰ ⟩
  ⟦ ⟪ γ ⟫ʰ ⟧ˢ ∘ ⟦ ⟪ δ ⟫ʰ ⟧ˢ
    ≈⟨ sym~~ (cong-∘ (hom∘sub γ) refl~~) ⟩ 
  γ ∘ ⟦ ⟪ δ ⟫ʰ ⟧ˢ
    ≈⟨ sym~~ (cong-∘ refl~~ (hom∘sub δ)) ⟩ 
  γ ∘ δ
    ∎
  where open EqR (HomS {_} {_})
 
hom∘sub p = p~⟦p⟧

hom∘sub <> = refl~~
hom∘sub < γ , x > = cong-<,> (cwf∘ws x) (hom∘sub γ)

sub∘hom [] = refl
sub∘hom (x ∷ ρ) = cong₂ _∙_ (sub∘hom ρ) (ws∘cwf x)

---------------------------------------------------------------------------
-- Lemmas to get the projection inverse proof right.

open Fins
open PProof

⟦map⟧~map : ∀ {m n} (is : Fins m n) →
            ⟦ mapTT var is ⟧ˢ ~~ mapT varCwf is
⟦map⟧~map <>         = refl~~
⟦map⟧~map < is , x > = cong-<,> refl~ (⟦map⟧~map is)

lm-p : ∀ n → vars (pFins n) ~~ ⟦ mapTT var (pFins n) ⟧ˢ
lm-p n = trans~~ (vars-map (pFins n)) (sym~~ (⟦map⟧~map (pFins n)))

lemmaₚ n rewrite sym (pp=p~ n) =
  trans~~ (vars-map (pFins n))
          (sym~~ (⟦map⟧~map (pFins n)))

{-
mapcwf : ∀ {m n} → (f : Fin m → Tm-cwf m) → Ren m n → Hom m n
mapcwf f [] = <>
mapcwf f (x ∷ is) = < mapcwf f is , f x >

pnm : ∀ {n} → Hom (suc n) n
pnm {n} = mapcwf varCwf pR

prop1 : ∀ {m n} (r : Ren m n) → ⟦ map var r ⟧ˢ ~~ mapcwf varCwf r
prop1 [] = trans~~ (sym~~ (idR <>)) (∘<> id)
prop1 (x ∷ r) = cong-<,> refl~ (prop1 r)

vr-lm : ∀ {m n} (r : Ren m n) → (mapcwf varCwf r) ∘ p ~~ mapcwf varCwf (map suc r)
vr-lm [] = ∘<> p
vr-lm (x ∷ r) = begin
  < mapcwf varCwf r , varCwf x > ∘ p ≈⟨ maps (varCwf x) (mapcwf varCwf r) p ⟩
  < mapcwf varCwf r ∘ p , varCwf x [ p ] > ≈⟨ cong-<,> refl~ (vr-lm r) ⟩
  < mapcwf varCwf (map suc r) , varCwf x [ p ] > ∎
  where open EqR (HomS {_} {_})

pnmvars : ∀ n → p ~~ pnm {n}
pnmvars zero = hom0~<> p
pnmvars (suc n) = begin
  p ≈⟨ eta p ⟩
  < p ∘ p , q [ p ] > ≈⟨ cong-<,> refl~ (cong-∘ (pnmvars n) refl~~) ⟩
  _ ≈⟨ cong-<,> refl~ (vr-lm pR) ⟩
  _ ≈⟨ {!!} ⟩
  {!!} ∎
  where open EqR (HomS {_} {_})
-}
