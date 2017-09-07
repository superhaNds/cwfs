module TermModels where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_] ; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate ; lookup-allFin)
open import Data.Fin using (Fin ; zero ; suc ; raise ; _+_ ; fromℕ)
open import Function using (_$_ ; _∘_)
open import Util using (_s∷_) -- snoc
open import WSModel
  renaming (q to qWS ; comp to compWS ; sub to subWS ; id to idW)
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

varUcwf : ∀ {n} (i : Fin n) → UcwfTm n
varUcwf zero = q _
varUcwf (suc i) = weakening (toUcwf (var _ i))

toUcwf (var n i) = varUcwf i

-- Auxiliary lemmas

idLemm : ∀ {n} (i : Fin n) → lookup i (idW n) ≡ i
idLemm i = lookup-allFin i

liftVar : ∀ n i → lift n (var n i) ≡ var (suc n) (suc i)
liftVar n i = cong (var (suc n)) (lookup∘tabulate suc i)

lookupIdLemma : (n : Nat) (i : Fin n) → lookup i (idSub n) ≡ var n i
lookupIdLemma n i = lookup∘tabulate (var n) i

lookupMap : ∀ {A B : Set} {f : A → B} (n : Nat) (i : Fin n) (xs : Vec A n)
               → f (lookup i xs) ≡ lookup i (map f xs)
lookupMap zero () _
lookupMap (suc n) zero (x ∷ xs) = refl
lookupMap (suc n) (suc i) (x ∷ xs) = lookupMap n i xs

lookupPLemma : (n : Nat)
               (i : Fin n) → lookup i (projSub n) ≡ var (suc n) (suc i)
lookupPLemma zero ()
lookupPLemma (suc n) zero = refl
lookupPLemma (suc n) (suc i) = begin
    lookup (suc i) (projSub (suc n))
  ≡⟨ refl ⟩
    lookup (suc i) (map (lift _) (idSub _))
  ≡⟨ sym (lookupMap _ (suc i) (idSub _)) ⟩
    (lift _) (lookup (suc i) (idSub (suc n)))
  ≡⟨ cong (lift _) (lookupIdLemma (suc n) (suc i)) ⟩
    (lift _) (var _ (suc i))
  ≡⟨ liftVar (suc n) (suc i) ⟩
    var (suc (suc n)) (suc (suc i))
  ∎

subID : ∀ n → (t : WellScopedTm n) → subWS n t n (idSub n) ≡ t
subID zero    (var _ ())
subID (suc n) (var _ x) = lookupIdLemma (suc n) x

-- Inverses

termInv₁ : ∀ {n} (t : WellScopedTm n) → t ≡ toWellscoped (toUcwf t)
termInv₂ : ∀ {n} (u : UcwfTm n) → u ≡ toUcwf (toWellscoped u)
substsInv₁ : ∀ {m n} → (v : Vec (WellScopedTm m) n) → v ≡ homToVec (vecToHom v)
substsInv₂ : ∀ {m n} → (h : HomCwf m n) → h ≡ vecToHom (homToVec h)

-- 
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

termInv₂ (q n) = refl
termInv₂ (sub m _ u (id _))
  rewrite subID _ (toWellscoped u) = sym $
    begin
      toUcwf (toWellscoped u)
    ≡⟨ sym $ termInv₂ u ⟩
      u
    ≡⟨ {!!} ⟩ -- sub on id law proves this
      sub m m u (id m)
    ∎
    
termInv₂ (sub n m u (comp _ k _ hkm hnk)) = {!!}
termInv₂ (sub _ m u (p _)) = {!!}
termInv₂ (sub n .0 u (<> _)) with toWellscoped u
termInv₂ (sub n _ u (<> _)) | var .0 ()
termInv₂ (sub n _ u (.n , k < h , x >)) = {!!}

substsInv₁ [] = refl
substsInv₁ (x ∷ xs)
  rewrite sym (substsInv₁ xs) |
          sym (termInv₁ x) = refl


substsInv₂ (id zero) = {!!} -- id₀ axiom proves this
substsInv₂ (id (suc m)) = {!!}
substsInv₂ (comp m n k hnk hmn) = {!!}
substsInv₂ (p n) = {!!} -- vecToHom never maps to p, 
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
