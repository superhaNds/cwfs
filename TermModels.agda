module TermModels where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup)
open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong)
open import Util using (_s∷_) -- snoc

-- without lam and app (yet)
data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n

idV : (n : Nat) → Vec (Fin n) n
idV zero    = []
idV (suc n) = (map suc (idV n)) s∷ zero

subw : (n : Nat) (t : WellScopedTm n) (m : Nat) (tms : Vec (WellScopedTm m) n) → WellScopedTm m
subw n (var _ x) m tms = lookup x tms

mutual 
  data UcwfTm : Nat → Set where
    q   : (n : Nat) → UcwfTm (suc n)
    sub : (m n : Nat) → UcwfTm n → HomCwf m n → UcwfTm m

  data HomCwf : Nat → Nat → Set where
    id‵   : (m : Nat) → HomCwf m m
    comp  : (m n k : Nat) → HomCwf n k → HomCwf m n → HomCwf m k
    p     : (n : Nat) → HomCwf (suc n) n
    ⟨⟩    : (m : Nat) → HomCwf m 0
    ⟨_,_⟩ : (m n : Nat) → HomCwf m n → UcwfTm m → HomCwf m (suc n)

homToVec : ∀ {m n : Nat} → HomCwf m n → Vec (WellScopedTm m) n
homToVec (id‵ n) = {!!}
homToVec (comp m n k hm_nk hm_mn) = let v_nk = homToVec hm_nk
                                        v_mn = homToVec hm_mn
                                    in {!!}
homToVec (p n) = {!!}
homToVec (⟨⟩ m) = []
homToVec (⟨ m , n ⟩ h x) = {!!}

vecToHom : ∀ {m n : Nat} → Vec (WellScopedTm m) n → HomCwf m n
vecToHom [] = ⟨⟩ _
vecToHom (x ∷ xs) = {!!}

toWellscoped : ∀ {n} (t : UcwfTm n) → WellScopedTm n
toWellscoped (q n)                = var (1 + n) zero
toWellscoped (sub m n ucwftm hom) = subw n (toWellscoped ucwftm) m (homToVec hom)

toUcwf : ∀ {n} (t : WellScopedTm n) → UcwfTm n
toUcwf (var _ zero)    = q _
toUcwf (var _ (suc x)) = {!!}

