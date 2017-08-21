module UcwfTerm where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Util using (_s∷_)

-- without lam and app (yet)
data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n

mutual 
  data DirectTm : Nat → Set where
    q : (n : Nat) → DirectTm (suc n)
    sub : (m n : Nat) → DirectTm n → HomCwf m n → DirectTm m

  data HomCwf : Nat → Nat → Set where
    id   : ∀ {m} → HomCwf m m
    comp : (m n k : Nat) → HomCwf n k → HomCwf m n → HomCwf m k
    p    : (n : Nat) → HomCwf (suc n) n

toWellscoped : ∀ {n} (t : DirectTm n) → WellScopedTm n
toWellscoped t = {!!}

toDirect : ∀ {n} (t : WellScopedTm n) → DirectTm n
toDirect t = {!!}

homToVec : ∀ {m n : Nat} → HomCwf m n → Vec (WellScopedTm m) n
homToVec h = {!!}

vecToHom : ∀ {m n : Nat} → Vec (WellScopedTm m) n → HomCwf m n
vecToHom v = {!!}
