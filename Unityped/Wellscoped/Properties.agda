module Unityped.Wellscoped.Properties where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ ; raise)
open import Function using (_∘_ ; _$_ ; flip)
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unityped.Wellscoped
open ≡-Reasoning

lookup-id : ∀ n i → lookup i (id n) ≡ var i
lookup-id _ i = lookup∘tabulate var i

lookupIn↑ : ∀ n i → lookup i (1toN n) ≡ suc i
lookupIn↑ n i = lookup∘tabulate suc i

lookupMap : ∀ {A B : Set} {f : A → B} (n : Nat) (i : Fin n) (xs : Vec A n)
              → f (lookup i xs) ≡ lookup i (map f xs)
lookupMap (suc n) zero    (x ∷ xs) = refl
lookupMap (suc n) (suc i) (x ∷ xs) = lookupMap n i xs

lookup-map : ∀ {A B : Set} (f : A → B) {n : Nat} (i : Fin n) (xs : Vec A n) →
             f (lookup i xs) ≡ lookup i (map f xs)
lookup-map f zero    (x ∷ xs) = refl
lookup-map f (suc i) (x ∷ xs) = lookup-map f i xs

suc-lookup-↑ : ∀ {m n} (r : Ren m n) (i : Fin n) → suc (lookup i r) ≡ lookup (suc i) (↑ r)
suc-lookup-↑ (i ∷ r) zero   = refl
suc-lookup-↑ r      (suc i) = lookup-map _ (suc i) r

lookup-pR : ∀ {n} (i : Fin n) → lookup i pR ≡ suc i
lookup-pR i = begin
  lookup i pR             ≡⟨⟩
  lookup i (map suc idF)  ≡⟨ cong (lookup i) (sym $ (tabulate-∘ suc Function.id)) ⟩
  lookup i (tabulate suc) ≡⟨ lookup∘tabulate suc i ⟩
  suc i                   ∎

wkVar : ∀ {n} i → weaken {n} (var i) ≡ var (suc i)
wkVar i = begin
  ren (var i) pR    ≡⟨⟩
  var (lookup i pR) ≡⟨ cong var (lookup-pR i) ⟩
  var (suc i)       ∎

lookup-p' : ∀ {n} i → lookup i (p' {n}) ≡ var (suc i)
lookup-p' i = begin
  lookup i (map weaken (id _)) ≡⟨ sym (lookupMap _ i (id _)) ⟩
  weaken (lookup i (id _))     ≡⟨ cong weaken (lookup-id _ i) ⟩
  weaken (var i)               ≡⟨ wkVar i ⟩
  var (suc i) ∎

lookup-p : ∀ {n} i → lookup i (p n) ≡ var (suc i)
lookup-p i = begin
  lookup i (tabulate (λ i → var (suc i))) ≡⟨ cong (lookup i) (tabulate-∘ var suc) ⟩
  lookup i (map var (tabulate suc))       ≡⟨ sym $ lookupMap _ i (tabulate suc) ⟩
  var (lookup i (tabulate suc))           ≡⟨ cong var (lookup∘tabulate suc i) ⟩
  var (suc i)                             ∎

p-lookup-eq : ∀ {n} i → lookup i (p n) ≡ lookup i (p' {n})
p-lookup-eq i = trans (lookup-p i) (sym (lookup-p' i))

allEqLookup : ∀ {A : Set} {n : Nat} (xs : Vec A n) (ys : Vec A n) →
               (∀ i → lookup i xs ≡ lookup i ys) → xs ≡ ys
allEqLookup []       []       _ = refl
allEqLookup (x ∷ xs) (y ∷ ys) φ = begin
  x ∷ xs  ≡⟨⟩
  _       ≡⟨ cong (_∷ xs) (φ zero) ⟩
  _       ≡⟨ sym (cong (_∷_ y) (allEqLookup ys xs (sym ∘ φ ∘ suc))) ⟩
  y ∷ ys  ∎

pS=p' : ∀ {n} → p n ≡ p' {n}
pS=p' = allEqLookup (p _) p' p-lookup-eq

tail-id-p : ∀ {n} → tail (id (1 + n)) ≡ p n
tail-id-p = refl

map-lookup-↑ : ∀ {n m} (ts : Subst m (1 + n)) →
               map (flip lookup ts) (1toN n) ≡ tail ts
map-lookup-↑ (t ∷ ts) = begin
  map (flip lookup (t ∷ ts)) (1toN _) ≡⟨ sym $ tabulate-∘ (flip lookup (t ∷ ts)) suc ⟩
  tabulate (flip lookup ts)           ≡⟨ tabulate∘lookup ts ⟩
  ts                                  ∎

p∘-lookup : ∀ {m n} (ts : Subst m (1 + n)) →
            p n ⊙ ts ≡ map (flip lookup ts) (1toN n)
p∘-lookup ts = begin
  map (_[ ts ]) (tabulate (λ x → var (suc x))) ≡⟨ cong (map (_[ ts ])) (tabulate-∘ var suc) ⟩
  map (_[ ts ]) (map var (tabulate suc))       ≡⟨⟩
  (map (_[ ts ]) ∘ map (var)) (1toN _)         ≡⟨ sym $ map-∘ (_[ ts ]) (var) (1toN _) ⟩
  map (λ i → (var i) [ ts ]) (1toN _)          ≡⟨⟩
  map (flip lookup ts) (1toN _)                ∎

↑-dist : ∀ {m n k} (r : Ren m n) (s : Ren k m) → ↑ (r ⊚ s) ≡ (↑ r ⊚ ↑ s)
↑-dist r s = begin
  ↑ (r ⊚ s)                                  ≡⟨⟩
  zero ∷ map suc (r ⊚ s)                     ≡⟨⟩
  zero ∷ map suc (map (flip lookup s) r)     ≡⟨ cong (zero ∷_) (sym (map-∘ suc (flip lookup s) r)) ⟩
  zero ∷ map (suc ∘ (flip lookup s)) r       ≡⟨ cong (zero ∷_) (map-cong (suc-lookup-↑ s) r) ⟩
  zero ∷ map ((flip lookup (↑ s)) ∘ suc) r   ≡⟨ cong (zero ∷_) (map-∘ (flip lookup (↑ s)) suc r) ⟩
  zero ∷ map (flip lookup (↑ s)) (map suc r) ≡⟨⟩
  ↑ r ⊚ ↑ s                                  ∎

⊚-asso : ∀ {m n k} (r : Ren m n) (s : Ren k m) (t : Term n) → ren t (r ⊚ s) ≡ ren (ren t r) s
⊚-asso r s (var i) = cong var (sym (lookup-map _ i r))
⊚-asso r s (`λ t) = begin
  `λ (ren t (↑ (r ⊚ s)))       ≡⟨ cong (`λ ∘ ren t) (↑-dist r s) ⟩
  `λ (ren t (↑ r ⊚ ↑ s))       ≡⟨ cong `λ (⊚-asso (↑ r) (↑ s) t) ⟩
  `λ (ren (ren t (↑ r)) (↑ s)) ∎
⊚-asso r s (t `$ u) = trans (cong (_`$ ren u (r ⊚ s)) (⊚-asso r s t))
                            (cong (ren (ren t r) s `$_) (⊚-asso r s u))

pR⊚-↑-map : ∀ {m n} (r : Ren m n) → pR ⊚ (↑ r) ≡ map suc r
pR⊚-↑-map r = begin
  pR ⊚ (↑ r)                                      ≡⟨⟩
  map (λ i → lookup i (↑ r)) (map suc idF)        ≡⟨ cong (map (λ i → lookup i (↑ r)))
                                                          (sym $ (tabulate-∘ suc Function.id)) ⟩
  map (λ i → lookup i (↑ r)) (tabulate suc)       ≡⟨ sym (tabulate-∘ _ suc) ⟩
  tabulate (flip lookup (zero ∷ map suc r) ∘ suc) ≡⟨⟩
  tabulate (flip lookup (map suc r))              ≡⟨ tabulate∘lookup (map suc r) ⟩
  map suc r                                       ∎

pR-⊚-↑ : ∀ {m n} (r : Ren m n) → r ⊚ pR ≡ pR ⊚ (↑ r) 
pR-⊚-↑ r = begin
  r ⊚ pR                 ≡⟨⟩
  map (flip lookup pR) r ≡⟨ map-cong lookup-pR r ⟩
  map suc r              ≡⟨ sym (pR⊚-↑-map r) ⟩
  pR ⊚ (↑ r)             ∎

pR-↑ : ∀ {m n} (r : Ren m n) (t : Term n) → ren (ren t r) pR ≡ ren (ren t pR) (↑ r)
pR-↑ r t = trans (sym (⊚-asso r pR t))
                 (sym $ begin
                   ren (ren t pR) (↑ r) ≡⟨ sym (⊚-asso pR (↑ r) t) ⟩
                   ren t (pR ⊚ (↑ r))   ≡⟨ cong (ren t) (sym $ pR-⊚-↑ r) ⟩
                   ren t (r ⊚ pR)       ∎)

↑ₛ-↑-dist : ∀ {m n k} (ts : Subst m n) (is : Ren k m) → ↑ₛ (ts ⊙r is) ≡ ↑ₛ ts ⊙r ↑ is
↑ₛ-↑-dist ts is = begin
  ↑ₛ (ts ⊙r is)                                           ≡⟨⟩
  var zero ∷ map (λ t → ren t pR) (ts ⊙r is)              ≡⟨ cong (var zero ∷_) (sym $ map-∘ _ _ ts) ⟩
  var zero ∷ map (λ t → ren (ren t is) pR) ts             ≡⟨ cong (var zero ∷_) (map-cong (pR-↑ is) ts) ⟩
  var zero ∷ map (λ t → ren (ren t pR) (↑ is)) ts         ≡⟨ cong (var zero ∷_) (map-∘ _ _ ts) ⟩
  var zero ∷ map (flip ren (↑ is)) (map (flip ren pR) ts) ≡⟨⟩
  map (flip ren (↑ is)) (var zero ∷ map (flip ren pR) ts) ≡⟨⟩
  ↑ₛ ts ⊙r ↑ is                                           ∎

map-lookup-pR : ∀ {m n k} (ts : Subst k m) (is : Ren m n) →
                map (λ i → ren (lookup i ts) pR) is ≡ map (flip lookup (↑ₛ ts)) (map suc is)
map-lookup-pR ts is = sym $ begin
  map (flip lookup (↑ₛ ts)) (map suc is)            ≡⟨ sym (map-∘ _ _ is) ⟩
  map (flip lookup (↑ₛ ts) ∘ suc) is                ≡⟨⟩
  map (λ i → lookup i (map (λ t → ren t pR) ts)) is ≡⟨ map-cong (λ i → sym (lookup-map (λ t → ren t pR) i ts)) is ⟩
  map (λ i → ren (lookup i ts) pR) is               ∎
  
↑-↑ₛ-dist : ∀ {m n k} (is : Ren m n) (ts : Subst k m) → ↑ₛ (is r⊙ ts) ≡ ↑ is r⊙ ↑ₛ ts
↑-↑ₛ-dist is ts = cong (var zero ∷_) (trans (sym (map-∘ _ _ is)) (map-lookup-pR ts is))

⊙r-asso : ∀ {m n k} (ts : Subst m n) (is : Ren k m) (t : Term n) →
          t [ ts ⊙r is ] ≡ ren (t [ ts ]) is
⊙r-asso ts is (var i)  = sym $ lookup-map (flip ren is) i ts
⊙r-asso ts is (t `$ u) = cong₂ _`$_ (⊙r-asso ts is t) (⊙r-asso ts is u)
⊙r-asso ts is (`λ t)   = trans (cong (`λ ∘ t [_]) (↑ₛ-↑-dist ts is))
                               (cong `λ (⊙r-asso (↑ₛ ts) (↑ is) t))

r⊙-asso : ∀ {m n k} (is : Ren m n) (ts : Subst k m) (t : Term n) →
          t [ is r⊙ ts ] ≡ (ren t is) [ ts ]
r⊙-asso is ts (var i)  = sym $ lookup-map (flip lookup ts) i is
r⊙-asso is ts (t `$ u) = cong₂ _`$_ (r⊙-asso is ts t) (r⊙-asso is ts u)
r⊙-asso is ts (`λ t)   = trans (cong (`λ ∘ t [_]) (↑-↑ₛ-dist is ts))
                               (cong `λ (r⊙-asso (↑ is) (↑ₛ ts) t))

⊙pR-↑ₛ : ∀ {m n} (ts : Subst m n) → ts ⊙r pR ≡ pR r⊙ (↑ₛ ts)
⊙pR-↑ₛ ts = sym $ trans (sym (map-∘ _ _ idF)) (map-lookup-allFin _)

↑ₛ-dist : ∀ {m n k} (ts : Subst m n) (us : Subst k m) → ↑ₛ (ts ⊙ us) ≡ (↑ₛ ts) ⊙ (↑ₛ us)
↑ₛ-dist ts us = begin
  ↑ₛ (ts ⊙ us)                                       ≡⟨⟩
  var zero ∷ map (λ t → ren t pR) (map (_[ us ]) ts) ≡⟨ cong (var zero ∷_) (sym (map-∘ _ _ ts)) ⟩
  var zero ∷ map (λ t → ren (t [ us ]) pR) ts        ≡⟨ cong (var zero ∷_) (map-cong (sym ∘ ⊙r-asso us pR) ts) ⟩
  var zero ∷ map (_[ us ⊙r pR ]) ts                  ≡⟨ cong (var zero ∷_) (map-cong (λ x → cong (x [_]) (⊙pR-↑ₛ us)) ts) ⟩
  var zero ∷ map (_[ pR r⊙ (↑ₛ us) ]) ts             ≡⟨ cong (var zero ∷_) (map-cong (r⊙-asso _ _) ts) ⟩
  var zero ∷ map (_[ ↑ₛ us ] ∘ flip ren pR) ts       ≡⟨ cong (var zero ∷_) (map-∘ _ _ ts) ⟩
  var zero ∷ map (_[ ↑ₛ us ]) (map (flip ren pR) ts) ≡⟨⟩
  map (_[ ↑ₛ us ]) (↑ₛ ts)                           ≡⟨⟩
  (↑ₛ ts) ⊙ (↑ₛ us)                                  ∎

⊙=⊙₂ : ∀ {m n k} (σ : Subst m n) (ω : Subst k m) → σ ⊙ ω ≡ σ ⊙₂ ω
⊙=⊙₂ [] ω = refl
⊙=⊙₂ (t ∷ σ) ω = cong (λ x → _ ∷ x) (⊙=⊙₂ σ ω)
