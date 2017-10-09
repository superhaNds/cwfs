{-# OPTIONS --allow-unsolved-metas #-}
module Unityped.Projections where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; tail ; tabulate)
open import Data.Vec.Properties
open import Data.Fin using (Fin ; zero ; suc ; fromℕ ; raise)
open import Function renaming (_∘_ to _◯_) using (_$_ ; flip)
open import Unityped.WSModel renaming (_∘_ to _∘'_ ; q to q~ ; id to id~ ; p to p~)
open import Unityped.UcwfModel renaming (_[_] to _`[_])
open import Unityped.Wellscoped.WsUcwf
open import Unityped.Wellscoped.Properties
open import Unityped.Isomorphism
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqR

postulate id0 : ∀ n → n + 0 ≡ n
postulate rsuc : ∀ n m → 1 + (n + m) ≡ n + (1 + m)

p` : (m n : Nat) → HomCwf (m + n) n
p` zero    n = id n
p` (suc m) n = p` m n ∘ p (m + n)

p`` : (m n : Nat) → HomCwf (m + n) n
p`` zero n = id n
p`` (suc m) n rewrite rsuc m n = p n ∘ p`` m (1 + n) -- but, p`` (1 + m) n and p n ∘ p`` m (1 + n) cannot be used interchangeably somewhere else

{- defined in WSModel
p^m : (m n : Nat) → Vec (WellScopedTm (m + n)) n
p^m zero    n = id n
p^m (suc m) n = p^m m n ∘ p (m + n)
-}

p=p : ∀ m n → p` m n ~ₕ p`` m n
p=p m n = {!!}

1q[p^m] : ∀ n m → q~ n ′[ p^m (m) (1 + n)] ≡ var (m + (1 + n)) (raise m (fromℕ n))
1q[p^m] n m = {!!}

-- p`` (1 + m) n : HomCwf (1 + (m + n)) n
-- p n ∘ p`` m (1 + n) : HomCwf (m + (1 + n)) n
bruh : (m n : Nat) → p` m n ~ₕ toHom (p^m m n)
bruh m zero rewrite p^m0 m = hom0~<> (p` m 0)
bruh m (suc n) = begin
  p` m (1 + n)                                    ≈⟨ eta $ p` m (1 + n) ⟩
  < p n ∘ p` m (1 + n) , q n `[ p` m (1 + n) ] >  ≈⟨ {!!} ⟩
  {!!} ∎
  where open EqR (HomCwfS {_} {_})
