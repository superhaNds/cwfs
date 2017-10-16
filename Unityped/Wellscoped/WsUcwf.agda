-------------------------------------------------------------------------------
-- Proofs of the equational laws of a ucwf and a λβ-ucwf for the wellscoped
-- terms.
-------------------------------------------------------------------------------

module Unityped.Wellscoped.WsUcwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function as Fun using (_∘_ ; _$_ ; flip ; const)
open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unityped.Ucwf
open import Unityped.Wellscoped.Properties
open import Unityped.Wellscoped.Syntax
open import Unityped.Wellscoped.Substitution
open import Unityped.Wellscoped.Beta
import Relation.Binary.EqReasoning as EqR
open ≡-Reasoning

-------------------------------------------------------------------------------
-- Term is a Ucwf

-- id = < p , q >

id=pq : ∀ {n} → id (1 + n) ≡ p n ∙ q
id=pq = refl

-- Substituting in the identity gives the same term

t[id] : ∀ {n} (t : Term n) → t [ id n ] ≡ t
t[id] (var i) = lookup-id _ i
t[id] (t · u) = trans (cong (_· u [ id _ ]) (t[id] t))
                      (cong (_·_ t) (t[id] u))
t[id] (ƛ t) = begin
  ƛ (t [ ↑ₛ id _ ])   ≡⟨⟩
  ƛ (t [ p' ∙ q ])    ≡⟨ cong (λ x → ƛ (t [ x ∙ q ])) (sym pS=p') ⟩
  ƛ (t [ p _ ∙ q ])   ≡⟨ cong (ƛ ∘ t [_]) (sym id=pq) ⟩
  ƛ (t [ id _ ])      ≡⟨ cong ƛ (t[id] t) ⟩
  ƛ t                 ∎

-- Substituting in a composition is applying the substitution to the first and the second
-- in succession

[]-asso : ∀ {m n k} (t : Term n) (ts : Subst m n) (us : Subst k m) →
          t [ ts ⋆ us ] ≡ t [ ts ] [ us ]
[]-asso (var ()) [] us 
[]-asso (var zero) (x ∷ ts) us = refl
[]-asso (var (suc i)) (x ∷ ts) us = []-asso (var i) ts us
[]-asso (t · u) ts us = cong₂ _·_ ([]-asso t ts us) ([]-asso u ts us)
[]-asso (ƛ t) ts us = trans (cong (ƛ ∘ t [_]) (↑ₛ-dist ts us))
                            (cong ƛ ([]-asso t (↑ₛ ts) (↑ₛ us)))

-- identity sub of zero

id₀[] : id 0 ≡ []
id₀[] = refl

-- the empty substitution is a left absorbing element (left zero)

∘-[] : ∀ {m n} (ts : Subst m n) → [] ⋆ ts ≡ []
∘-[] _ = refl

-- Composing with the projection substitution drops the last element

p⋆Cons : ∀ {n k} (t : Term n) (σ : Subst n k) → p k ⋆ (σ ∙ t) ≡ σ
p⋆Cons t σ = trans (p∘-lookup (σ ∙ t)) (map-lookup-↑ (σ ∙ t))

-- Category of substitutions

-- Composing substitutions is associative

⋆-asso : ∀ {m n k j} (σ : Subst m n) (γ : Subst k m) (δ : Subst j k) →
         σ ⋆ (γ ⋆ δ) ≡ (σ ⋆ γ) ⋆ δ
⋆-asso [] γ δ = refl
⋆-asso (t ∷ σ) γ δ = begin
  (σ ∙ t) ⋆ (γ ⋆ δ)              ≡⟨⟩
  σ ⋆ (γ ⋆ δ) ∙ t [ γ ⋆ δ ]      ≡⟨ cong (λ x → x ∷ _) ([]-asso t γ δ) ⟩
  σ ⋆ (γ ⋆ δ) ∙ t [ γ ] [ δ ]    ≡⟨ cong (t [ γ ] [ δ ] ∷_) (⋆-asso σ γ δ) ⟩
  (σ ⋆ γ) ⋆ δ ∙ t [ γ ] [ δ ]    ∎

-- Left identity sub

∘-lid : ∀ {m n} (σ : Subst m n) → id n ⋆ σ ≡ σ
∘-lid [] = refl
∘-lid (x ∷ σ) = begin
  id _ ⋆ (σ ∙ x)        ≡⟨ ⋆=⋆₂ (id _)  (σ ∙ x) ⟩
  p _  ⋆₂ (σ ∙ x) ∙ x   ≡⟨ cong (_∙ x) (sym $ ⋆=⋆₂ (p _) (σ ∙ x)) ⟩
  p _ ⋆ (σ ∙ x) ∙ x     ≡⟨ cong (_∙ x) (p⋆Cons x σ) ⟩
  σ ∙ x                 ∎

-- Right identity sub

∘-rid : ∀ {m n} (σ : Subst m n) → σ ⋆ id m  ≡ σ
∘-rid [] = refl
∘-rid (t ∷ σ) rewrite t[id] t
                    | ∘-rid σ = refl

-- Substituting the De Bruijn zero variable takes the last element

q[] : ∀ {m n} (t : Term m) (σ : Subst m n) → q [ σ ∙ t ] ≡ t
q[] _ _ = refl

-- Composing with a cons (by definition)

maps : ∀ {m n} (t : Term n) (σ : Subst n m) (γ : Subst m n) →
       (σ ∙ t) ⋆ γ ≡ (σ ⋆ γ) ∙ t [ γ ]
maps t σ γ = refl
{-
Term-Ucwf : Ucwf Term
Term-Ucwf = record
              { id    = id
              ; <>    = []
              ; p     = p
              ; q     = vr 0
              ; _∘_   = _⋆_
              ; _[_]  = _[_]
              ; <_,_> = _∙_
              ; id₀   = id₀[]
              ; ∘<>   = ∘-[]
              ; varp  = id=pq
              ; idL   = ∘-lid
              ; idR   = ∘-rid
              ; assoc = λ σ₁ σ₂ → sym ∘ (⋆-asso σ₁ σ₂)
              ; terId = t[id]
              ; pCons = p⋆Cons
              ; qCons = q[]
              ; clos  = []-asso
              ; maps  = maps
              }

---------------------------------------------------------------------------------------
-- Term is also a Ucwf with lambda, application, and β

η′ : ∀ {n} (t : Term n) → ƛ (t [ p n ] · q) ~ t
η′ t rewrite sym (wk-[p] t) = η t

abs : ∀ {n m} (t : Term (1 + n)) (σ : Subst m n) → ƛ t [ σ ] ~ ƛ (t [ σ ⋆ p m ∙ q ])
abs t σ rewrite mapWk-⋆p σ = refl~

Term-λβ-ucwf : λβ-ucwf Term _~_
Term-λβ-ucwf = record
                 { ucwf = Term-Ucwf
                 ; ƛ    = ƛ
                 ; _·_  = _·_
                 ; β    = β
                 ; η    = η′
                 ; app  = λ _ _ _ → refl~
                 ; abs  = abs
                 }
-}
