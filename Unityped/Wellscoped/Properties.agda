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

lookupIn↑ : ∀ n i → lookup i (↑ n) ≡ suc i
lookupIn↑ n i = lookup∘tabulate suc i

lookupMap : ∀ {A B : Set} {f : A → B} (n : Nat) (i : Fin n) (xs : Vec A n)
              → f (lookup i xs) ≡ lookup i (map f xs)
lookupMap (suc n) zero    (x ∷ xs) = refl
lookupMap (suc n) (suc i) (x ∷ xs) = lookupMap n i xs

lookupInP : ∀ n i → lookup i (p′ n) ≡ var (suc n) (suc i)
lookupInP n i = begin
  lookup i (map (var (suc n)) (↑ n)) ≡⟨ sym (lookupMap n i (↑ n)) ⟩
  var (suc n) (lookup i (↑ n))       ≡⟨ cong (var (suc n)) (lookupIn↑ n i) ⟩
  var (suc n) (suc i)                ∎ 

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
  lookup i (p n)             ≡⟨⟩
  lookup i (map lift (id n)) ≡⟨ sym (lookupMap n i (id n)) ⟩
  lift (lookup i (id n))     ≡⟨ cong lift (lookupInId n i) ⟩
  lift (var n i)             ≡⟨ liftVar n i ⟩
  var (suc n) (suc i)        ∎

lookupInPs : ∀ {n} i → lookup i (p′ n) ≡ lookup i (p n)
lookupInPs i = begin
  lookup i (p′ _)     ≡⟨ lookupInP _ i ⟩
  var (suc _) (suc i) ≡⟨ sym (lookupPLemma _ i) ⟩
  lookup i (p _)      ∎

id=id′ : ∀ n → id n ≡ id′ n
id=id′ n = tabulate-allFin (var n)

p=p' : ∀ n → p n ≡ p′ n
p=p' n = allEqLookup (p n) (p′ n) (sym ◯ lookupInPs)

subVarP : ∀ n i → (var n i) ′[ p n ] ≡ var (suc n) (suc i)
subVarP = lookupPLemma

postulate tss : ∀ n t →  lift (lam n t) ≡ (lam n t ′[ p n ])

subLift : ∀ n x → lift x ≡ x ′[ p n ]
subLift n (var _ i)   = trans (liftVar _ i) (sym (subVarP _ i))
subLift n (lam _ t)   = tss n t
subLift n (app _ t u) = trans (cong (λ x → app _ x _) (subLift _ t))
                              (cong (λ x → app _ _ x) (subLift _ u))

lift∘p : ∀ {n m : Nat} (xs : Vec (WellScopedTm n) m) → map lift xs ≡ xs ∘ p n
lift∘p []       = refl
lift∘p (x ∷ xs) = trans (cong (λ s → s ∷ _) (subLift _ x))
                        (cong (λ s → _ ∷ s) (lift∘p xs))

tailIdp : ∀ n → tail (id (suc n)) ≡ p n
tailIdp n  = sym $ begin
  p n                ≡⟨ p=p' n ⟩
  p′ n               ≡⟨⟩
  tail (id′ (suc n)) ≡⟨ cong tail (sym (id=id′ $ 1 + n)) ⟩ 
  tail (id (suc n))  ∎

∘=∘₁ : ∀ {m n k} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n) → ts ∘ us ≡ ts ∘₁ us
∘=∘₁ [] us       = refl
∘=∘₁ (x ∷ ts) us = cong (x ′[ us ] ∷_) (∘=∘₁ ts us)

∘₁=∘₂ : ∀ {m n k} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n) → ts ∘₁ us ≡ ts ∘₂ us
∘₁=∘₂ ts us = begin
  map (_′[ us ]) ts                          ≡⟨ cong (λ x → map _ x) (sym (tabulate∘lookup ts)) ⟩
  map (_′[ us ]) (tabulate (flip lookup ts)) ≡⟨ sym (tabulate-∘ (_′[ us ]) (flip lookup ts)) ⟩
  tabulate (λ i → lookup i ts ′[ us ])       ∎

∘=∘₂ : ∀ {m n k} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n) → ts ∘ us ≡ ts ∘₂ us
∘=∘₂ ts us = sym $ trans (sym (∘₁=∘₂ ts us)) (sym (∘=∘₁ ts us))

map-lookup-↑ : ∀ {n m} (ts : Vec (WellScopedTm m) (1 + n)) →
               map (flip lookup ts) (↑ n) ≡ tail ts
map-lookup-↑ (t ∷ ts) = begin
  map (flip lookup (t ∷ ts)) (↑ _) ≡⟨ sym $ tabulate-∘ (flip lookup (t ∷ ts)) suc ⟩
  tabulate (flip lookup ts)        ≡⟨ tabulate∘lookup ts ⟩
  ts                               ∎

p∘-lookup : ∀ {m n} (ts : Vec (WellScopedTm m) (1 + n)) →
            p′ n ∘ ts ≡ map (flip lookup ts) (↑ n)
p∘-lookup ts = begin
  p′ _ ∘ ts                           ≡⟨ ∘=∘₁ (p′ _) ts ⟩
  map (_′[ ts ]) (map (var _) (↑ _))  ≡⟨ sym $ map-∘ (_′[ ts ]) (var _) (↑ _) ⟩
  map (λ i → (var _ i) ′[ ts ]) (↑ _) ≡⟨⟩
  map (flip lookup ts) (↑ _)          ∎
