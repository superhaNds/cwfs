module UcwfModel where

open import Data.Nat
  renaming (ℕ to Nat)
  using (zero ; suc)

data UcwfTm : Nat → Set
data HomCwf : Nat → Nat → Set

data UcwfTm where
  q   : (n : Nat) → UcwfTm (suc n)
  sub : (m n : Nat) → UcwfTm n → HomCwf m n → UcwfTm m

data HomCwf where
  id       : (m : Nat) → HomCwf m m
  comp     : (m n k : Nat) → HomCwf n k → HomCwf m n → HomCwf m k
  p        : (n : Nat) → HomCwf (suc n) n
  <>       : (m : Nat) → HomCwf m zero
  _,_<_,_> : (m n : Nat) → HomCwf m n → UcwfTm m → HomCwf m (suc n)

weakening : ∀ {n : Nat} → UcwfTm n → UcwfTm (suc n)
weakening t = sub (suc _) _ t (p _)
