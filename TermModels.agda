module TermModels where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup)
open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong)
open import Util using (_s∷_) -- snoc

data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n

idV : (n : Nat) → Vec (Fin n) n
idV zero    = []
idV (suc n) = (map suc (idV n)) s∷ zero

subWS : (n : Nat) (t : WellScopedTm n) (m : Nat) (tms : Vec (WellScopedTm m) n) → WellScopedTm m
subWS n (var _ x) m tms = lookup x tms

idS : ∀ n → Vec (WellScopedTm n) n
idS zero = []
idS (suc n) = {!!} s∷ var (suc n) zero

vec∘ : ∀ {m n k} → Vec (WellScopedTm m) n → Vec (WellScopedTm n) k → Vec (WellScopedTm m) k
vec∘ vmn [] = []
vec∘ vmn (x ∷ vnk) = vec∘ vmn vnk s∷ subWS _ x _ vmn

ext : ∀ {m n} → Vec (WellScopedTm m) n → WellScopedTm m → Vec (WellScopedTm m) (suc n)
ext [] t = t ∷ []
ext (x ∷ xs) t = ext xs t s∷ t

weaken : ∀ {m n} → Vec (WellScopedTm m) n → Vec (WellScopedTm (suc m)) n
weaken [] = []
weaken (x ∷ xs) = (weaken xs) s∷ var _ zero

data UcwfTm : Nat → Set

data HomCwf : Nat → Nat → Set

data UcwfTm where
  q   : (n : Nat) → UcwfTm (suc n)
  sub : (m n : Nat) → UcwfTm n → HomCwf m n → UcwfTm m

data HomCwf where
  id‵      : (m : Nat) → HomCwf m m
  comp     : (m n k : Nat) → HomCwf n k → HomCwf m n → HomCwf m k
  p        : (n : Nat) → HomCwf (suc n) n
  <>       : (m : Nat) → HomCwf m 0
  _,_<_,_> : (m n : Nat) → HomCwf m n → UcwfTm m → HomCwf m (suc n)

toUcwf : ∀ {n} (t : WellScopedTm n) → UcwfTm n
toWellscoped : ∀ {n} (t : UcwfTm n) → WellScopedTm n
homToVec : ∀ {m n : Nat} → HomCwf m n → Vec (WellScopedTm m) n
vecToHom : ∀ {m n : Nat} → Vec (WellScopedTm m) n → HomCwf m n

homToVec (id‵ n) = idS n
homToVec (comp m n k hm_nk hm_mn) =
  let v_nk = homToVec hm_nk
      v_mn = homToVec hm_mn
  in vec∘ v_mn v_nk
homToVec (p n) = {!!}
homToVec (<> m) = []
homToVec (m , n < h , t >) =
  let wst = toWellscoped t
      wsv = homToVec h
  in ext wsv wst

vecToHom [] = <> _
vecToHom (x ∷ xs) = {!!}

toWellscoped (q n)                = var (1 + n) zero
toWellscoped (sub m n ucwftm hom) = subWS n (toWellscoped ucwftm) m (homToVec hom)

toUcwf (var _ zero)    = q _
toUcwf (var _ (suc i)) = {!!}
