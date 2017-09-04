module TermModels where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_])
open import Data.Fin using (Fin ; zero ; suc)
open import Util using (_s∷_) -- snoc
open import WSModel renaming (comp to compV ; sub to subWS)
open import UcwfModel
  using (UcwfTm ; HomCwf ; id ; comp ; <> ; p ; q ; sub ; _,_<_,_>)

-- Translation functions
toUcwf       : ∀ {n} → WellScopedTm n → UcwfTm n
toWellscoped : ∀ {n} → UcwfTm n → WellScopedTm n
homToVec     : ∀ {m n} → HomCwf m n → Vec (WellScopedTm m) n
vecToHom     : ∀ {m n} → Vec (WellScopedTm m) n → HomCwf m n

homToVec (id n) = idSub n
homToVec (comp m n k hnk hmn) =
  let vnk = homToVec hnk
      vmn = homToVec hmn
  in compV vmn vnk
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

toUcwf (var _ zero) = q _
toUcwf (var _ (suc x)) = {!!}
--sub (suc n) (suc n) (q n) (id‵ (suc n))
