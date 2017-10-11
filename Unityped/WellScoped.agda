module Unityped.WellScoped where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Function as Fun using (_∘_ ; _$_ ; flip)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

infix 10 _`$_
infix 8 _⊚_
infix 8 _⊙_
infix 8 _⊙r_
infix 8 _r⊙_

data Term (n : Nat) : Set where
  var   : (i : Fin n) → Term n
  `λ    : (t : Term (1 + n)) → Term n
  _`$_  : (t₁ t₂ : Term n) → Term n

Sub : (Nat → Set) → Nat → Nat → Set
Sub T m n = Vec (T m) n

Ren : Nat → Nat → Set
Ren m n = Sub Fin m n

↑_ : ∀ {m n} → Ren m n → Ren (1 + m) (1 + n)
↑ r = zero ∷ map suc r

idF : ∀ {n} → Ren n n
idF = tabulate Fun.id

ren : ∀ {n m} → Term n → Ren m n → Term m
ren (var i) r  = var (lookup i r)
ren (`λ t)   r = `λ (ren t (↑ r))
ren (t `$ u) r = (ren t r) `$ (ren u r)

_⊚_ : ∀ {m n k} → Ren m n → Ren k m → Ren k n
r₁ ⊚ r₂ = map (flip lookup r₂) r₁

wkR : ∀ m {n} → Ren (m + n) n
wkR zero    = idF
wkR (suc m) = map suc (wkR m) 

pR : ∀ {n} → Ren (1 + n) n
pR = wkR 1

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
  lookup i (map suc idF)  ≡⟨ cong (lookup i) (sym $ (tabulate-∘ suc Fun.id)) ⟩
  lookup i (tabulate suc) ≡⟨ lookup∘tabulate suc i ⟩
  suc i                   ∎

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
                                                          (sym $ (tabulate-∘ suc Fun.id)) ⟩
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

Subst : Nat → Nat → Set
Subst m n = Sub Term m n

ren2sub : ∀ {m n} → Ren m n → Subst m n
ren2sub = map var

↑ₛ_ : ∀ {m n} → Subst m n → Subst (1 + m) (1 + n)
↑ₛ ts = var zero ∷ map (λ t → ren t pR) ts

_[_] : ∀ {m n} → Term n → Subst m n → Term m
var i    [ ts ] = lookup i ts
`λ t     [ ts ] = `λ (t [ ↑ₛ ts ])
(t `$ u) [ ts ] = t [ ts ] `$ u [ ts ]

_⊙_ : ∀ {m n k} → Subst m n → Subst k m → Subst k n
ts ⊙ us = map (_[ us ]) ts

_r⊙_ : ∀ {m n k} → Ren m n → Subst k m → Subst k n
is r⊙ ts = map (flip lookup ts) is

_⊙r_ : ∀ {m n k} → Subst m n → Ren k m → Subst k n
ts ⊙r is = map (flip ren is) ts

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
  map (_[ ↑ₛ us ]) (↑ₛ ts) ≡⟨⟩
  (↑ₛ ts) ⊙ (↑ₛ us) ∎

[]-asso : ∀ {m n k} (ts : Subst m n) (us : Subst k m) (t : Term n) →
          t [ ts ⊙ us ] ≡ t [ ts ] [ us ]
[]-asso [] us (var ())
[]-asso (x ∷ ts) us (var zero) = refl
[]-asso (x ∷ ts) us (var (suc i)) = []-asso ts us (var i)
[]-asso ts us (t `$ u) = cong₂ _`$_ ([]-asso ts us t) ([]-asso ts us u)
[]-asso ts us (`λ t) = trans (cong (`λ ∘ t [_]) (↑ₛ-dist ts us))
                             (cong `λ ([]-asso (↑ₛ ts) (↑ₛ us) t))
