module WSModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; allFin ; tabulate)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_)
open import Util using (_s∷_) -- snoc
open import Relation.Binary.PropositionalEquality

data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n

------------------ Aux ------------------
id : (n : Nat) → Vec (Fin n) n
id = allFin

↑_ : ∀ n → Vec (Fin (suc n)) n
↑ _ = tabulate suc

rename : (n : Nat) (t : WellScopedTm n) (m : Nat) (is : Vec (Fin m) n) → WellScopedTm m
rename n (var _ i) m is = var m (lookup i is)
-----------------------------------------

-- Corresponding Ucwf terms --

-- q
q : (n : Nat) → WellScopedTm (suc n)
q n = var (suc n) zero

-- id
idSub : ∀ n → Vec (WellScopedTm n) n
idSub n = tabulate (var n)

-- sub
sub : (n : Nat) (t : WellScopedTm n) (m : Nat) (tms : Vec (WellScopedTm m) n) → WellScopedTm m
sub n (var _ x) m tms = lookup x tms

-- comp of homs
comp : ∀ {m n k} → Vec (WellScopedTm m) n → Vec (WellScopedTm n) k → Vec (WellScopedTm m) k
comp _   [] = []
comp vmn (t ∷ vnk) = (comp vmn vnk) s∷ sub _ t _ vmn

-- weakening (derived)
lift : (n : Nat) → WellScopedTm n → WellScopedTm (suc n)
lift n t = rename n t (suc n) (↑ n)

-- p
projSub : (n : Nat) → Vec (WellScopedTm (suc n)) n
projSub = map (lift _) ∘ idSub --  --λ n → tabulate (λ x → lift n (var n x))
--map (lift _) ∘ idSub -- 

-- < Δ , τ >
ext : ∀ {m n} → Vec (WellScopedTm m) n → WellScopedTm m → Vec (WellScopedTm m) (suc n)
ext ts t = t ∷ ts

-- <>
empt : ∀ {m} → Vec (WellScopedTm m) zero
empt = []
