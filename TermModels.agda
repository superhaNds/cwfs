module TermModels where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_])
open import Data.Fin using (Fin ; zero ; suc ; raise)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong)
open import Util using (_s∷_) -- snoc

data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n

idV : (n : Nat) → Vec (Fin n) n
idV zero    = []
idV (suc n) = (map suc (idV n)) s∷ zero

idS : (n : Nat) → Vec (WellScopedTm n) n
idS = λ n → map (var n) (idV n)

↑_ : (n : Nat) → Vec (Fin (suc n)) n
↑ zero = []
↑ suc n = (map suc (↑ n)) s∷ suc zero

rename : (n : Nat) (t : WellScopedTm n) (m : Nat) (is : Vec (Fin m) n) → WellScopedTm m
rename n (var .n i) m is = var m (lookup i is)

lift : (n : Nat) → WellScopedTm n → WellScopedTm (suc n)
lift n t = rename n t (suc n) (↑ n)

subWS : (n : Nat) (t : WellScopedTm n) (m : Nat) (tms : Vec (WellScopedTm m) n) → WellScopedTm m
subWS n (var _ x) m tms = lookup x tms

vec∘ : ∀ {m n k} → Vec (WellScopedTm m) n → Vec (WellScopedTm n) k → Vec (WellScopedTm m) k
vec∘ vmn [] = []
vec∘ vmn (t ∷ vnk) = vec∘ vmn vnk s∷ (subWS _ t _ vmn)

projSub : (n : Nat) → Vec (WellScopedTm (suc n)) n
projSub = map (lift _) ∘ idS
        
--weaken : ∀ {m : Nat} → WellScopedTm m → WellScopedTm (suc m)
--weaken t = subWS _ t _ (projSub _)

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

weakening : ∀ {n : Nat} → UcwfTm n → UcwfTm (suc n)
weakening t = sub (suc _) _ t (p _)

-- Translation functions
toUcwf       : ∀ {n} → WellScopedTm n → UcwfTm n
toWellscoped : ∀ {n} → UcwfTm n → WellScopedTm n
homToVec     : ∀ {m n} → HomCwf m n → Vec (WellScopedTm m) n
vecToHom     : ∀ {m n} → Vec (WellScopedTm m) n → HomCwf m n

homToVec (id‵ n) = idS n
homToVec (comp m n k hm_nk hm_mn) =
  let v_nk = homToVec hm_nk
      v_mn = homToVec hm_mn
  in vec∘ v_mn v_nk
homToVec (p n) = projSub n
homToVec (<> m) = []
homToVec (m , n < h , t >) =
  let t′ = toWellscoped t
      h′ = homToVec h
  in {!!} -- replace the last variable with t ?

vecToHom [] = <> _
vecToHom (x ∷ xs) = {!!}

toWellscoped (q n)                = var (suc n) zero
toWellscoped (sub m n ucwftm hom) = subWS n (toWellscoped ucwftm) m (homToVec hom)

toUcwf (var zero ())
toUcwf (var (suc n) zero) = q n
toUcwf (var (suc n) (suc x)) = {!!} --sub (suc n) (suc n) (q n) (id‵ (suc n))
