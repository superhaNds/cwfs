module TermModels where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_] ; reverse)
open import Data.Fin using (Fin ; zero ; suc ; raise ; _+_ ; fromℕ)
open import Function using (_$_ ; _∘_)
open import Util using (_s∷_) -- snoc
open import WSModel renaming (q to qWS ; comp to compWS ; sub to subWS)
open import Iso
open import UcwfModel
open import Relation.Binary.PropositionalEquality
 using (_≡_ ; refl ; sym ; trans ; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Translation functions
toUcwf       : ∀ {n} → WellScopedTm n → UcwfTm n
toWellscoped : ∀ {n} → UcwfTm n → WellScopedTm n
homToVec     : ∀ {m n} → HomCwf m n → Vec (WellScopedTm m) n
vecToHom     : ∀ {m n} → Vec (WellScopedTm m) n → HomCwf m n

homToVec (id n)               = idSub n
homToVec (comp m n k hnk hmn) = compWS (homToVec hmn) (homToVec hnk)
homToVec (p n)                = projSub n
homToVec (<> m)               = empt
homToVec (m , n < h , t >)    = ext (homToVec h) (toWellscoped t)

vecToHom []       = <> _
vecToHom (x ∷ xs) = _ , _ < vecToHom xs , toUcwf x >

toWellscoped (q n)         = qWS n
toWellscoped (sub m n t h) = subWS n (toWellscoped t) m (homToVec h)

toUcwf (var _ zero)    = q _
toUcwf (var _ (suc x)) = weakening (toUcwf (var _ x))

-- Inverse proofs

lookupPLemma : (n : Nat) (i : Fin n) → lookup i (projSub n) ≡ var (suc n) (suc i)
lookupPLemma zero ()
lookupPLemma (suc n) i = {!!}

termInv₁ : ∀ {n} (t : WellScopedTm n) → t ≡ toWellscoped (toUcwf t)
termInv₁ (var _ zero) = refl
termInv₁ (var _ (suc x)) = sym $
  begin
    subWS _ (toWellscoped (toUcwf (var _ x))) (suc _) (projSub _)
  ≡⟨ sym (cong (λ t → subWS _ t (suc _) (projSub _)) (termInv₁ (var _ x))) ⟩
    subWS _ (var _ x) (suc _) (projSub _)
  ≡⟨ refl ⟩
    lookup x (projSub _)
  ≡⟨ lookupPLemma _ x ⟩
    var (suc _) (suc x)
  ∎

termInv₂ : ∀ {n} (u : UcwfTm n) → u ≡ toUcwf (toWellscoped u)
termInv₂ (q n) = refl
termInv₂ (sub n m u h) = {!!}
{-
termInv₂ (sub n m u h) with homToVec h | toWellscoped u
termInv₂ (sub n .0 u h) | [] | var .0 ()
termInv₂ (sub n _ u h) | x ∷ xs | var _ zero  = {!!}
termInv₂ (sub n _ u h) | x ∷ xs | var _ (suc i) = {!!}
-}
substsInv₁ : ∀ {m n} → (v : Vec (WellScopedTm m) n) → v ≡ homToVec (vecToHom v)
substsInv₁ [] = refl
substsInv₁ (x ∷ xs)
  rewrite sym (substsInv₁ xs) |
          sym (termInv₁ x) = refl

substsInv₂ : ∀ {m n} → (h : HomCwf m n) → h ≡ vecToHom (homToVec h)
substsInv₂ (id zero) = {!!} -- id₀ axiom proves this
substsInv₂ (id (suc m)) = {!!}
substsInv₂ (comp m n k hnk hmn) = {!!}
substsInv₂ (p n) = {!!}
substsInv₂ (<> m) = refl
substsInv₂ (m , n < h , x >)
  rewrite sym (substsInv₂ h) |
          sym (termInv₂ x) = refl

wellscoped≅ucwf : ∀ {n} → WellScopedTm n ≅ UcwfTm n
wellscoped≅ucwf =
  record { to = toUcwf
         ; from = toWellscoped
         ; inv₁ = termInv₁
         ; inv₂ = termInv₂ }
