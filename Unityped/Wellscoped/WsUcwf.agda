{- 

Proofs of the equational laws of a unityped category with families for the scope
safe lambda calculus terms.

-}
module Unityped.Wellscoped.WsUcwf where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Function as Fun using (_∘_ ; _$_ ; flip)
open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unityped.Ucwf
open import Unityped.Wellscoped.Properties
open import Unityped.Wellscoped
open ≡-Reasoning

id=pq : ∀ {n} → id (1 + n) ≡ p n ∙ q n
id=pq = refl

t[id] : ∀ {n} (t : Term n) → t [ id n ] ≡ t
t[id] (var i) = lookup-id _ i
t[id] (t `$ u) = trans (cong (_`$ u [ id _ ]) (t[id] t))
                       (cong (_`$_ t) (t[id] u))
t[id] (`λ t)= begin
  `λ (t [ ↑ₛ id _ ])   ≡⟨⟩
  `λ (t [ p' ∙ q _ ])  ≡⟨ cong (λ x → `λ (t [ x ∙ q _ ])) (sym pS=p') ⟩
  `λ (t [ p _ ∙ q _ ]) ≡⟨ cong (`λ ∘ t [_]) (sym id=pq) ⟩
  `λ (t [ id _ ])      ≡⟨ cong `λ (t[id] t) ⟩
  `λ t                 ∎

[]-asso : ∀ {m n k} (t : Term n) (ts : Subst m n) (us : Subst k m) →
          t [ ts ⊙ us ] ≡ t [ ts ] [ us ]
[]-asso (var ()) [] us 
[]-asso (var zero) (x ∷ ts) us = refl
[]-asso (var (suc i)) (x ∷ ts) us = []-asso (var i) ts us
[]-asso (t `$ u) ts us = cong₂ _`$_ ([]-asso t ts us) ([]-asso u ts us)
[]-asso (`λ t) ts us = trans (cong (`λ ∘ t [_]) (↑ₛ-dist ts us))
                             (cong `λ ([]-asso t (↑ₛ ts) (↑ₛ us)))

id₀[] : id 0 ≡ []
id₀[] = refl

∘-[] : ∀ {m n} (ts : Subst m n) → [] ⊙ ts ≡ []
∘-[] _ = refl

⊙-asso : ∀ {m n k j} (σ : Subst m n) (γ : Subst k m) (δ : Subst j k) →
         σ ⊙ (γ ⊙ δ) ≡ (σ ⊙ γ) ⊙ δ
⊙-asso [] γ δ = refl
⊙-asso (t ∷ σ) γ δ = begin
  (σ ∙ t) ⊙ (γ ⊙ δ)           ≡⟨⟩
  σ ⊙ (γ ⊙ δ) ∙ t [ γ ⊙ δ ]   ≡⟨ cong (λ x → x ∷ _) ([]-asso t γ δ) ⟩
  σ ⊙ (γ ⊙ δ) ∙ t [ γ ] [ δ ] ≡⟨ cong (t [ γ ] [ δ ] ∷_) (⊙-asso σ γ δ) ⟩
  (σ ⊙ γ) ⊙ δ ∙ t [ γ ] [ δ ] ∎

p⊙Cons : ∀ {n k} (t : Term n) (σ : Subst n k) → p k ⊙ (σ ∙ t) ≡ σ
p⊙Cons t σ = trans (p∘-lookup (σ ∙ t)) (map-lookup-↑ (σ ∙ t))

∘-lid : ∀ {m n} (σ : Subst m n) → id n ⊙ σ ≡ σ
∘-lid [] = refl
∘-lid (x ∷ σ) = begin
  id _ ⊙ (σ ∙ x)      ≡⟨ ⊙=⊙₂ (id _)  (σ ∙ x) ⟩
  p _  ⊙₂ (σ ∙ x) ∙ x ≡⟨ cong (_∙ x) (sym $ ⊙=⊙₂ (p _) (σ ∙ x)) ⟩
  p _ ⊙ (σ ∙ x) ∙ x   ≡⟨ cong (_∙ x) (p⊙Cons x σ) ⟩
  σ ∙ x               ∎

∘-rid : ∀ {m n} (σ : Subst m n) → σ ⊙ id m  ≡ σ
∘-rid [] = refl
∘-rid (t ∷ σ) rewrite t[id] t
                    | ∘-rid σ = refl

q[] : ∀ {m n} (t : Term m) (σ : Subst m n) → q n [ σ ∙ t ] ≡ t
q[] _ _ = refl

maps : ∀ {m n} (t : Term n) (σ : Subst n m) (γ : Subst m n) →
       (σ ∙ t) ⊙ γ ≡ (σ ⊙ γ) ∙ t [ γ ]
maps t σ γ = refl

Term-Ucwf : Ucwf Term
Term-Ucwf = record
              { id    = id
              ; <>    = []
              ; p     = p
              ; q     = q
              ; _∘_   = _⊙_
              ; _[_]  = _[_]
              ; <_,_> = _∙_
              ; id₀   = id₀[]
              ; ∘<>   = ∘-[]
              ; varp  = id=pq
              ; idL   = ∘-lid
              ; idR   = ∘-rid
              ; assoc = λ α β γ → sym (⊙-asso α β γ)
              ; terId = t[id]
              ; pCons = p⊙Cons
              ; qCons = q[]
              ; clos  = []-asso
              ; maps  = maps
              }
