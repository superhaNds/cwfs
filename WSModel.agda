module WSModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_)
open import Util using (_s∷_) -- snoc

-- without lambda and app, yet...
data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n

id : (n : Nat) → Vec (Fin n) n
id zero    = []
id (suc n) = (map suc (id n)) s∷ zero

idSub : (n : Nat) → Vec (WellScopedTm n) n
idSub = λ n → map (var n) (id n)

↑_ : (n : Nat) → Vec (Fin (suc n)) n
↑ zero = []
↑ suc n = (map suc (↑ n)) s∷ suc zero

rename : (n : Nat) (t : WellScopedTm n) (m : Nat) (is : Vec (Fin m) n) → WellScopedTm m
rename n (var _ i) m is = var m (lookup i is)

lift : (n : Nat) → WellScopedTm n → WellScopedTm (suc n)
lift n t = rename n t (suc n) (↑ n)

sub : (n : Nat) (t : WellScopedTm n) (m : Nat) (tms : Vec (WellScopedTm m) n) → WellScopedTm m
sub n (var _ x) m tms = lookup x tms

comp : ∀ {m n k} → Vec (WellScopedTm m) n → Vec (WellScopedTm n) k → Vec (WellScopedTm m) k
comp _   [] = []
comp vmn (t ∷ vnk) = (comp vmn vnk) s∷ sub _ t _ vmn

projSub : (n : Nat) → Vec (WellScopedTm (suc n)) n
projSub = map (lift _) ∘ idSub

