-------------------------------------------------------------------------------
-- Proof of Scwf axioms for the concrete typed lambda calculus
-------------------------------------------------------------------------------
module SimpTyped.Old.ImpSub.Tm-Scwf where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import Function as F using (_$_ ; flip)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import SimpTyped.Old.Type
open import SimpTyped.Old.Context
open import SimpTyped.Old.ImpSub.Syntax
open import SimpTyped.Old.ImpSub.Properties
open import SimpTyped.Old.Scwf
open P.≡-Reasoning

-------------------------------------------------------------------------------
-- Axiom proofs

idExt : ∀ {Γ α} → id {Γ ∙ α} ≡ (p , q)
idExt = refl

-- empty morphism is a left zero

ttLzero : ∀ {Γ Δ} (ρ : Sub Γ Δ) → tt ∘ ρ ≡ tt
ttLzero _ = refl

-- q is the second projection

qCons : ∀ {Γ Δ α} (t : Tm Γ α) (ρ : Sub Γ Δ) → q [ ρ , t ] ≡ t
qCons t ρ = refl

-- p is the first projection

pCons : ∀ {Δ Θ α} (t : Tm Δ α) (γ : Sub Δ Θ) → p ∘ (γ , t) ≡ γ

-- id is a left identity in composition

idL : ∀ {Γ Δ} (ρ : Sub Δ Γ) → id ∘ ρ ≡ ρ

pCons {Θ = Θ} t = trans (∘-step Θ id _ t) F.∘ idL

idL {ε}     tt      = refl
idL {Γ ∙ α} (ρ , t) = cong (_, t) (pCons t ρ)

-- associativity of substitution

subComp : ∀ {Γ Δ Θ α} (t : Tm Γ α) (γ : Sub Δ Γ) (δ : Sub Θ Δ)
          → t [ γ ∘ δ ] ≡ t [ γ ] [ δ ]
subComp (var here) γ δ = refl
subComp (var (there ∈Γ)) (γ , u) δ = subComp (var ∈Γ) γ δ            
subComp (t · u) γ δ = cong₂ _·_ (subComp t γ δ) (subComp u γ δ)
subComp {Γ} {Δ} (ƛ t) γ δ = sym $ cong ƛ $ trans (
     sym (subComp t (wk γ , q)
                    (wk δ , q)))
     ((cong (t [_] F.∘ (_, q))
            (trans (∘-step Γ γ (wk-sub Δ ⊆-∙ δ) q)
                   (wk-∘ Γ ⊆-∙ γ δ))))

-- associativity of composition

assoc : ∀ {Γ Δ Θ Λ} (γ : Sub Δ Θ) (δ : Sub Γ Δ) (ζ : Sub Λ Γ)
         → (γ ∘ δ) ∘ ζ ≡ γ ∘ (δ ∘ ζ)
assoc {Θ = ε}     tt      δ ζ = refl
assoc {Θ = Θ ∙ _} (γ , t) δ ζ =
  trans (cong ((γ ∘ δ) ∘ ζ ,_) (sym (subComp t δ ζ)))
        (cong (_, t [ δ ∘ ζ ]) (assoc γ δ ζ))

-- composition on the right maps to cons

compExt : ∀ {Γ Δ} {α : Ty} (t : Tm Δ α) (γ : Sub Δ Γ) (δ : Sub Γ Δ) →
        (γ , t) ∘ δ ≡ (γ ∘ δ , (t [ δ ]))
compExt = λ _ _ _ → refl       

-- scwf record instantiation

TmScwf : Scwf
TmScwf = record
           { Ty = Ty
           ; Ctx = Ctx
           ; Tm = Tm
           ; Sub = Sub
           ; ⋄ = ε
           ; _∙_ = _∙_
           ; _≈_ = _≡_
           ; _≋_ = _≡_
           ; IsEquivT = P.isEquivalence
           ; IsEquivS = P.isEquivalence
           ; id = id
           ; _∘_ = _∘_
           ; _[_] = _[_]
           ; <> = tt
           ; <_,_> = _,_
           ; p = p
           ; q = q
           ; id₀ = id₀
           ; left-zero = ttLzero
           ; idExt = idExt
           ; idL = idL
           ; idR = idR
           ; assoc = assoc
           ; subId = subId
           ; pCons = pCons
           ; qCons = qCons
           ; subComp = subComp
           ; compExt = compExt
           ; cong-sub = cong-sub
           ; cong-<,> = cong-,
           ; cong-∘ = cong-∘
           }

-- here we use the fact that γ ∘ p is the same as weakening γ

subLam : ∀ {Γ Δ} {α β} (t : Tm (Γ ∙ α) β) (γ : Sub Δ Γ)
         → ƛ (t [ wk γ , q ]) ≡ ƛ (t [ γ ∘ p , q ])
subLam {α = α} t γ rewrite sym (wk-sub-∘-p {α = α} γ)= refl        

TmLamScwf : Lambda-scwf
TmLamScwf = record
              { scwf = TmScwf
              ; _`→_ = _⇒_
              ; lam = ƛ
              ; app = _·_
              ; subApp = λ _ _ _ → refl
              ; subLam = subLam
              ; cong-lam = ƛ-eq
              ; cong-app = app-eq
              }
