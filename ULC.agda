module ULC where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Nary using (_^_ ; proj ; map^ ; id)

data Term : Nat → Set where
  var : (n : Nat) → Fin n → Term n
  lam : (n : Nat) → Term (suc n) → Term n
  app : (n : Nat) → Term n → Term n → Term n

I : Term 0
I = lam 0 (var 1 zero)

K : Term 0
K = lam 0 (lam 1 (var (suc (suc zero)) (suc zero)))

↑_ : (n : Nat) → Fin (suc n) ^ n
↑ zero  = tt
↑ suc n = map^ suc n (↑ n) , suc zero

rename : (n : Nat) (t : Term n) (m : Nat) (is : Fin m ^ n) → Term m
rename n (var _ i)   m is = var m (proj n i is)
rename n (lam _ t)   m is = lam m (rename (suc n) t (suc m) (map^ suc n is , zero))
rename n (app _ t u) m is = app m (rename n t m is) (rename n u _ is)

lift : (n : Nat) → Term n → Term (suc n)
lift n t = rename n t (suc n) (↑ n)

sub : (n : Nat) (t : Term n) (m : Nat) (fs : Term m ^ n) → Term m
sub n (var _ i)   _ fs = proj n i fs
sub n (lam _ t)   m fs = lam m (sub (suc n) t (suc m) (map^ (lift m) n fs , (var (suc m) zero)))
sub n (app _ t u) m fs = app m (sub n t m fs) (sub n u _ fs)

data _~_⇒_ : (n : Nat) (t₁ t₂ : Term n) → Set where
  varcong : (n : Nat) (i : Fin n) → n ~ var n i ⇒ var n i
  ξ       : (n : Nat) (f g : Term (suc n)) (_ : suc n ~ f ⇒ g) → n ~ lam n f ⇒ lam n g
  apcong  : (n : Nat) (h h′ : Term n) (_ : n ~ h ⇒ h)
              (f f′ : Term n) (_ : n ~ f ⇒ f′) → n ~ app n h f ⇒ app n h′ f′
  β       : (n : Nat) (g : Term (suc n)) (f : Term n)
              → n ~ app n (lam n g) f ⇒ sub (suc n) g n (map^ (var n) n (id n) , f)
  symm     : (n : Nat) (f g : Term n) (_ : n ~ f ⇒ g) → n ~ g ⇒ f
  transt   : (n : Nat) (f g h : Term n) (_ : n ~ f ⇒ g) (_ : n ~ g ⇒ h) → n ~ f ⇒ h

reflx : ∀ (n : Nat) (t : Term n) → n ~ t ⇒ t
reflx n (var _ x)   = varcong n x
reflx n (lam _ t)   = ξ n t t (reflx (suc n) t)
reflx n (app _ t u) = apcong n t t (reflx n t) u u (reflx n u)
