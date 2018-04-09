module ExpSub where

open import Data.Nat renaming (ℕ to Nat) using (_+_ ; suc ; zero)
open import Relation.Binary using (Setoid ; IsEquivalence)
import Relation.Binary.EqReasoning as EqR
open import Ucwf

data Tm  : Nat → Set
data Sub : Nat → Nat → Set

data Tm where
  q    : ∀ {n} → Tm (suc n)
  _[_] : ∀ {m n} → Tm n → Sub m n → Tm m 

data Sub where
  id    : ∀ {n} → Sub n n
  _∙_   : ∀ {m n k} → Sub m n → Sub k m → Sub k n
  p     : ∀ {n} → Sub (suc n) n
  <>    : ∀ {n} → Sub n 0
  <_,_> : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)

infix 4 _~_
infix 4 _≈_

data _~_ : {n : Nat} → Tm n → Tm n → Set
data _≈_ : {m n : Nat} → Sub m n → Sub m n → Set

data _~_ where
  q-sub : ∀ {m n} {ρ : Sub m n} {t} → q [ < ρ , t > ] ~ t

  subId : ∀ {n} {t : Tm n} → t [ id ] ~ t

  subComp : ∀ {m n k} {t} {ρ : Sub m n} {σ : Sub k m}
            → t [ ρ ∙ σ ] ~ t [ ρ ] [ σ ]

  cong-sub : ∀ {m n} {ρ σ : Sub m n} {t u}
             → t ~ u
             → ρ ≈ σ
             → t [ ρ ] ~ u [ σ ]

  sym~ : ∀ {n} {t₁ t₂ : Tm n}
         → t₁ ~ t₂
         → t₂ ~ t₁

  trans~ : ∀ {n} {t₁ t₂ t₃ : Tm n}
           → t₁ ~ t₂
           → t₂ ~ t₃
           → t₁ ~ t₃

refl~ : ∀ {n} {t : Tm n} → t ~ t
refl~ = trans~ (sym~ subId) subId

data _≈_ where
  left-zero : ∀ {n m} {ρ : Sub n m} → <> ∙ ρ ≈ <>

  id-zero : id {0} ≈ <>

  idL : ∀ {m n} {ρ : Sub m n} → id ∙ ρ ≈ ρ

  idR : ∀ {m n} {ρ : Sub m n} → ρ ∙ id ≈ ρ

  ∙-asso : ∀ {m n k j} {ρ₁ : Sub n k} {ρ₂ : Sub m n} {ρ₃ : Sub j m}
           → (ρ₁ ∙ ρ₂) ∙ ρ₃ ≈ ρ₁ ∙ (ρ₂ ∙ ρ₃)

  p-∙ : ∀ {m n} {ρ : Sub m n} {t} → p ∙ < ρ , t > ≈ ρ

  idExt : ∀ {n} → id {1 + n} ≈ < p , q >

  compExt : ∀ {m n k} {σ : Sub n m} {ρ : Sub k n} {t}
            → < σ , t > ∙ ρ ≈ < σ ∙ ρ , t [ ρ ] >

  cong-<,> : ∀ {m n} {σ ρ : Sub m n} {t u}
             → t ~ u
             → σ ≈ ρ
             → < σ , t > ≈ < ρ , u >

  cong-∙ : ∀ {m n k} {σ₁ σ₂ : Sub n k} {ρ₁ ρ₂ : Sub m n}
           → σ₁ ≈ σ₂
           → ρ₁ ≈ ρ₂
           → σ₁ ∙ ρ₁ ≈ σ₂ ∙ ρ₂

  sym≈ : ∀ {m n} {ρ₁ ρ₂ : Sub m n}
         → ρ₁ ≈ ρ₂
         → ρ₂ ≈ ρ₁

  trans≈ : ∀ {m n} {ρ₁ ρ₂ ρ₃ : Sub m n}
           → ρ₁ ≈ ρ₂
           → ρ₂ ≈ ρ₃
           → ρ₁ ≈ ρ₃

refl≈ : ∀ {m n} {ρ : Sub m n} → ρ ≈ ρ
refl≈ = trans≈ (sym≈ idL) idL


cong-sub₁ : ∀ {m n} {γ : Sub m n} {t u} → t ~ u → t [ γ ] ~ u [ γ ]
cong-sub₁ t~u = cong-sub t~u refl≈

cong-sub₂ : ∀ {m n} {γ δ : Sub m n} {t} → γ ≈ δ → t [ γ ] ~ t [ δ ]
cong-sub₂ γ≈δ = cong-sub refl~ γ≈δ

cong-<, : ∀ {m n} {γ σ : Sub m n} {t} → γ ≈ σ → < γ , t > ≈ < σ , t >
cong-<, γ≈σ = cong-<,> refl~ γ≈σ

cong-,> : ∀ {m n} {γ : Sub m n} {t u} → t ~ u → < γ , t > ≈ < γ , u >
cong-,> t~u = cong-<,> t~u refl≈

cong-∙₁ : ∀ {m n k} {γ σ : Sub n k} {δ : Sub m n} →
          γ ≈ σ → γ ∙ δ ≈ σ ∙ δ
cong-∙₁ γ≈σ = cong-∙ γ≈σ refl≈

cong-∙₂ : ∀ {m n k} {γ : Sub n k} {δ σ : Sub m n} →
          δ ≈ σ → γ ∙ δ ≈ γ ∙ σ
cong-∙₂ δ≈σ = cong-∙ refl≈ δ≈σ 

ExpSubUcwf : Ucwf
ExpSubUcwf = record
               { Tm  = Tm
               ; Sub = Sub
               ; _~_ = _~_
               ; _≈_ = _≈_
               ; IsEquivT =
                   record
                     { refl = refl~
                     ; sym = sym~
                     ; trans = trans~ }
               ; IsEquivS =
                   record
                     { refl = refl≈
                      ; sym = sym≈
                      ; trans = trans≈ }
               ; id        = id
               ; _∘_       = _∙_
               ; _[_]      = _[_]
               ; <>        = <>
               ; <_,_>     = <_,_>
               ; p         = p
               ; q         = q
               ; id-zero   = id-zero
               ; left-zero = left-zero
               ; idExt     = idExt
               ; idL       = idL
               ; idR       = idR
               ; assoc     = ∙-asso
               ; subId     = subId
               ; pCons     = p-∙
               ; qCons     = q-sub
               ; subComp   = subComp 
               ; compExt   = compExt
               ; cong-<,>  = cong-<,>
               ; cong-sub  = cong-sub
               ; cong-∘    = cong-∙
               }

open Ucwf.Ucwf ExpSubUcwf using (setoidTm ; setoidSub)

TmSetoid : ∀ {n} → Setoid _ _
TmSetoid {n} = setoidTm {n}

SubSetoid : ∀ {m n} → Setoid _ _
SubSetoid {m} {n} = setoidSub {m} {n}

emptySub : ∀ {n} (ρ : Sub n zero) → ρ ≈ <>
emptySub ρ = begin
  ρ           ≈⟨ sym≈ idL ⟩
  id {0} ∙ ρ  ≈⟨ cong-∙₁ id-zero ⟩
  <> ∙ ρ      ≈⟨ left-zero ⟩ 
  <>
  ∎
  where open EqR (SubSetoid {_} {_})

surj-<,> : ∀ {n m} (ρ : Sub m (suc n)) → ρ ≈ < p ∙ ρ , q [ ρ ] >
surj-<,> ρ = begin
  ρ                    ≈⟨ sym≈ idL ⟩
  id ∙ ρ               ≈⟨ cong-∙₁ idExt  ⟩
  < p , q > ∙ ρ        ≈⟨ compExt ⟩
  < p ∙ ρ , q [ ρ ] >
  ∎
  where open EqR (SubSetoid {_} {_})
