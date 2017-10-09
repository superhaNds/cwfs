{-# OPTIONS --allow-unsolved-metas #-}
module Unityped.Wellscoped.Properties where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc ; fromℕ)
open import Function renaming (_∘_ to _◯_) using (_$_ ; flip)
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Unityped.WSModel
open ≡-Reasoning

liftVar : ∀ n i → lift (var n i) ≡ var (suc n) (suc i)
liftVar n i = cong (var (suc n)) (lookup∘tabulate suc i)

lookupInId : ∀ n i → lookup i (id n) ≡ var n i
lookupInId n i = lookup∘tabulate (var n) i

lookupIn↑ : ∀ n i → lookup i (1toN n) ≡ suc i
lookupIn↑ n i = lookup∘tabulate suc i

lookupMap : ∀ {A B : Set} {f : A → B} (n : Nat) (i : Fin n) (xs : Vec A n)
              → f (lookup i xs) ≡ lookup i (map f xs)
lookupMap (suc n) zero    (x ∷ xs) = refl
lookupMap (suc n) (suc i) (x ∷ xs) = lookupMap n i xs

lookupInP : ∀ n i → lookup i (p′ n) ≡ var (suc n) (suc i)
lookupInP n i = begin
  lookup i (map (var (suc n)) (1toN n)) ≡⟨ sym (lookupMap n i (1toN n)) ⟩
  var (suc n) (lookup i (1toN n))       ≡⟨ cong (var (suc n)) (lookupIn↑ n i) ⟩
  var (suc n) (suc i)                   ∎ 

lookup-up : ∀ n i → lookup i (up n) ≡ suc (suc i)
lookup-up n i = lookup∘tabulate (λ z → suc (suc z)) i

allEqLookup : ∀ {A : Set} {n : Nat} (xs : Vec A n) (ys : Vec A n) →
               (∀ i → lookup i xs ≡ lookup i ys) → xs ≡ ys
allEqLookup []       []       _ = refl
allEqLookup (x ∷ xs) (y ∷ ys) φ = begin
  x ∷ xs ≡⟨⟩
  _      ≡⟨ cong (_∷ xs) (φ zero) ⟩
  _      ≡⟨ sym (cong (_∷_ y) (allEqLookup ys xs (sym ◯ φ ◯ suc))) ⟩
  y ∷ ys ∎

lookupPLemma : ∀ n i → lookup i (p n) ≡ var (suc n) (suc i)
lookupPLemma n i = begin
  lookup i (p n)         ≡⟨⟩
  lookup i (↑ (id n))    ≡⟨ sym (lookupMap n i (id n)) ⟩
  lift (lookup i (id n)) ≡⟨ cong lift (lookupInId n i) ⟩
  lift (var n i)         ≡⟨ liftVar n i ⟩
  var (suc n) (suc i)    ∎

lookupInPs : ∀ {n} i → lookup i (p′ n) ≡ lookup i (p n)
lookupInPs i = begin
  lookup i (p′ _)     ≡⟨ lookupInP _ i ⟩
  var (suc _) (suc i) ≡⟨ sym (lookupPLemma _ i) ⟩
  lookup i (p _)      ∎

id=id′ : ∀ n → id n ≡ id′ n
id=id′ n = tabulate-allFin (var n)

p=p' : ∀ n → p n ≡ p′ n
p=p' n = allEqLookup (p n) (p′ n) (sym ◯ lookupInPs)

suc1toN : ∀ {n : Nat} → map suc (tabulate suc) ≡ up n
suc1toN = sym (tabulate-∘ suc suc)

subVarP : ∀ n i → (var n i) ′[ p n ] ≡ var (suc n) (suc i)
subVarP = lookupPLemma

postulate tss : ∀ n t →  lift (lam n t) ≡ (lam n t ′[ p n ])
postulate lams : ∀ {n m} (t : WellScopedTm (1 + n))  (us : VecTerm m n) → lift (lam n t ′[ us ]) ≡ lift (lam n t) ′[ q _ ∷ ↑ us ] 

liftSub : ∀ {n m} (t : WellScopedTm n) (us : Vec (WellScopedTm m) n) →
          lift (t ′[ us ]) ≡ lift t ′[ (q _ ∷ ↑ us) ]
liftSub (var _ zero) (x ∷ us) = refl
liftSub (var _ (suc i)) (x ∷ us) = begin
  lift (var _ (suc i) ′[ x ∷ us ]) ≡⟨⟩
  lift (lookup (suc i) (x ∷ us))   ≡⟨⟩
  lift (lookup i us)               ≡⟨ liftSub (var _ i) us ⟩
  lookup (lookup i (1toN _)) _     ≡⟨ cong (λ z → lookup z _) (lookupIn↑ _ i) ⟩
  lookup (suc i) (q _ ∷ ↑ us)      ≡⟨⟩
  lookup i (↑ us)                  ≡⟨ sym $ begin
    lookup (lookup i (up _)) (q _ ∷ ↑ (x ∷ us)) ≡⟨ cong (λ z → lookup z _) (lookup-up _ i) ⟩
    lookup (suc (suc i)) (q _ ∷ lift x ∷ ↑ us)  ≡⟨⟩
    lookup i (↑ us)                             ∎ ⟩
  _ ∎
liftSub (lam n t) us = lams t us
{-begin
  lift (lam _ (t ′[ q _ ∷ ↑ us ]))                             ≡⟨⟩
  lam _ (rename (t ′[ q _ ∷ ↑ us ]) (zero ∷ map suc (1toN _))) ≡⟨ {!!} ⟩
  lam _ (rename t (zero ∷ map suc (1toN _))
               ′[ q _ ∷ ↑ (q _ ∷ ↑ us)])                       ∎-}
liftSub (app n t u) us = trans (cong (λ x → app _ x _) (liftSub t us))
                               (cong (λ x → app _ _ x) (liftSub u us))

liftDist : ∀ {m n k} (ts : VecTerm n k) (us : VecTerm m n) →
           ↑ (ts ∘ us) ≡ ↑ ts ∘ (q _ ∷ ↑ us)
liftDist [] us = refl
liftDist (x ∷ ts) us = trans (cong (λ z → z ∷ _) (liftSub x us))
                             (cong (lift x ′[ q _ ∷ ↑ us ] ∷_)
                                   (liftDist ts us))

subLift : ∀ n x → lift x ≡ x ′[ p n ]
subLift n (var _ i)   = trans (liftVar _ i) (sym (subVarP _ i))
subLift n (lam _ t)   = tss n t
subLift n (app _ t u) = trans (cong (λ x → app _ x _) (subLift _ t))
                              (cong (λ x → app _ _ x) (subLift _ u))

lift∘p : ∀ {n m : Nat} (xs : Vec (WellScopedTm n) m) → ↑ xs ≡ xs ∘ p n
lift∘p []       = refl
lift∘p (x ∷ xs) = trans (cong (λ s → s ∷ _) (subLift _ x))
                        (cong (λ s → _ ∷ s) (lift∘p xs))

tailIdp : ∀ n → tail (id (1 + n)) ≡ p n
tailIdp n  = sym $ begin
  p n                ≡⟨ p=p' n ⟩
  p′ n               ≡⟨⟩
  tail (id′ (suc n)) ≡⟨ cong tail (sym (id=id′ $ 1 + n)) ⟩ 
  tail (id (suc n))  ∎

∘=∘₁ : ∀ {m n k} (ts : VecTerm n k) (us : VecTerm m n) → ts ∘ us ≡ ts ∘₁ us
∘=∘₁ [] us       = refl
∘=∘₁ (x ∷ ts) us = cong (x ′[ us ] ∷_) (∘=∘₁ ts us)

∘₁=∘₂ : ∀ {m n k} (ts : VecTerm n k) (us : VecTerm m n) → ts ∘₁ us ≡ ts ∘₂ us
∘₁=∘₂ ts us = begin
  map (_′[ us ]) ts                          ≡⟨ cong (λ x → map _ x) (sym (tabulate∘lookup ts)) ⟩
  map (_′[ us ]) (tabulate (flip lookup ts)) ≡⟨ sym (tabulate-∘ (_′[ us ]) (flip lookup ts)) ⟩
  tabulate (λ i → lookup i ts ′[ us ])       ∎

∘=∘₂ : ∀ {m n k} (ts : VecTerm n k) (us : VecTerm m n) → ts ∘ us ≡ ts ∘₂ us
∘=∘₂ ts us = trans (∘=∘₁ ts us) (∘₁=∘₂ ts us)

map-lookup-↑ : ∀ {n m} (ts : VecTerm m (1 + n)) →
               map (flip lookup ts) (1toN n) ≡ tail ts
map-lookup-↑ (t ∷ ts) = begin
  map (flip lookup (t ∷ ts)) (1toN _) ≡⟨ sym $ tabulate-∘ (flip lookup (t ∷ ts)) suc ⟩
  tabulate (flip lookup ts)           ≡⟨ tabulate∘lookup ts ⟩
  ts                                  ∎

p∘-lookup : ∀ {m n} (ts : VecTerm m (1 + n)) →
            p′ n ∘ ts ≡ map (flip lookup ts) (1toN n)
p∘-lookup ts = begin
  p′ _ ∘ ts                               ≡⟨ ∘=∘₁ (p′ _) ts ⟩
  (map (_′[ ts ]) ◯ map (var _)) (1toN _) ≡⟨ sym $ map-∘ (_′[ ts ]) (var _) (1toN _) ⟩
  map (λ i → (var _ i) ′[ ts ]) (1toN _)  ≡⟨⟩
  map (flip lookup ts) (1toN _)           ∎
