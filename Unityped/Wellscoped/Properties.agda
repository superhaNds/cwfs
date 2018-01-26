-----------------------------------------------------------------------------------------
-- Properties and lemmata required for proving the laws of a Ucwf for the well-scoped
-- lambda calculus terms and other.
-----------------------------------------------------------------------------------------

module Unityped.Wellscoped.Properties where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ ; raise)
open import Function as F using (_$_ ; flip)
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unityped.Wellscoped.Syntax
open import Unityped.Wellscoped.Substitution
open ≡-Reasoning
  
-----------------------------------------------------------------------------------------
-- Properties mostly relating lookups in substitutions, renamings, weakening

abstract

  lookup-id : ∀ {n} i → lookup i (id {n}) ≡ var i
  lookup-id i = lookup∘tabulate var i

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

  suc-lookup-↑ : ∀ {m n} (r : Ren m n) (i : Fin n) → suc (lookup i r) ≡ lookup (suc i) (lift-ren r)
  suc-lookup-↑ (i ∷ r) zero   = refl
  suc-lookup-↑ r      (suc i) = lookup-map _ (suc i) r

  lookup-pR : ∀ {n} (i : Fin n) → lookup i pR ≡ suc i
  lookup-pR i = begin
    lookup i pR              ≡⟨⟩
    lookup i (map suc idF)   ≡⟨ cong (lookup i) (sym $ (tabulate-∘ suc F.id)) ⟩
    lookup i (tabulate suc)  ≡⟨ lookup∘tabulate suc i ⟩
    suc i                    ∎

  wkVar : ∀ {n} i → weaken {n} (var i) ≡ var (suc i)
  wkVar i = begin
    ren (var i) pR     ≡⟨⟩
    var (lookup i pR)  ≡⟨ cong var (lookup-pR i) ⟩
    var (suc i)        ∎

  lookup-p' : ∀ {n} i → lookup i (p' {n}) ≡ var (suc i)
  lookup-p' {n} i = begin
    lookup i (weaken-subst id)   ≡⟨ sym (lookupMap _ i (id {n})) ⟩
    weaken (lookup i (id {n}))   ≡⟨ cong weaken (lookup-id i) ⟩
    weaken (var i)               ≡⟨ wkVar i ⟩
    var (suc i)                  ∎

  lookup-p : ∀ {n} i → lookup i (p {n}) ≡ var (suc i)
  lookup-p i = begin
    lookup i (tabulate (λ i → var (suc i)))  ≡⟨ cong (lookup i) (tabulate-∘ var suc) ⟩
    lookup i (map var (tabulate suc))        ≡⟨ sym $ lookupMap _ i (tabulate suc) ⟩
    var (lookup i (tabulate suc))            ≡⟨ cong var (lookup∘tabulate suc i) ⟩
    var (suc i)                              ∎

  p-lookup-eq : ∀ {n} i → lookup i p ≡ lookup i (p' {n})
  p-lookup-eq i = trans (lookup-p i) (sym (lookup-p' i))

  allEqLookup : ∀ {A : Set} {n : Nat} (xs : Vec A n) (ys : Vec A n) →
                 (∀ i → lookup i xs ≡ lookup i ys) → xs ≡ ys
  allEqLookup []       []       _ = refl
  allEqLookup (x ∷ xs) (y ∷ ys) φ = begin
    x ∷ xs    ≡⟨⟩
    _         ≡⟨ cong (_∷ xs) (φ zero) ⟩
    _         ≡⟨ sym (cong (_∷_ y) (allEqLookup ys xs (sym F.∘ φ F.∘ suc))) ⟩
    y ∷ ys    ∎

  pp=p~ : ∀ n → pp n ≡ p {n}
  pp=p~ n = allEqLookup (pp n) p (λ i → trans (lookup-mapTT i) (sym (lookup-p i)))

  p=p' : ∀ {n} → p {n} ≡ p' {n}
  p=p' = allEqLookup p p' p-lookup-eq

  tail-id-p : ∀ {n} → tail (id {1 + n}) ≡ p {n}
  tail-id-p = refl

  map-lookup-↑ : ∀ {n m} (ts : Subst m (1 + n)) →
                 map (flip lookup ts) (1toN n) ≡ tail ts
  map-lookup-↑ (t ∷ ts) = begin
    map (flip lookup (t ∷ ts)) (1toN _)   ≡⟨ sym $ tabulate-∘ (flip lookup (t ∷ ts)) suc ⟩
    tabulate (flip lookup ts)             ≡⟨ tabulate∘lookup ts ⟩
    ts                                    ∎

  p∘-lookup : ∀ {m n} (ts : Subst m (1 + n)) →
              p {n} ∘ ts ≡ map (flip lookup ts) (1toN n)
  p∘-lookup ts = begin
    map (_[ ts ]) (tabulate (λ x → var (suc x)))  ≡⟨ cong (map (_[ ts ])) (tabulate-∘ var suc) ⟩
    map (_[ ts ]) (map var (tabulate suc))        ≡⟨⟩
    (map (_[ ts ]) F.∘ map (var)) (1toN _)        ≡⟨ sym $ map-∘ (_[ ts ]) (var) (1toN _) ⟩
    map (λ i → (var i) [ ts ]) (1toN _)           ≡⟨⟩
    map (flip lookup ts) (1toN _)                 ∎

  lift-dist : ∀ {m n k} (r : Ren m n) (s : Ren k m) → lift-ren (r ⊚ s) ≡ (lift-ren r ⊚ lift-ren s)
  lift-dist r s = begin
    lift-ren (r ⊚ s)                                   ≡⟨⟩
    zero ∷ map suc (r ⊚ s)                             ≡⟨⟩
    zero ∷ map suc (map (flip lookup s) r)             ≡⟨ cong (zero ∷_) (sym (map-∘ suc (flip lookup s) r)) ⟩
    zero ∷ map (suc F.∘ (flip lookup s)) r             ≡⟨ cong (zero ∷_) (map-cong (suc-lookup-↑ s) r) ⟩
    zero ∷ map ((flip lookup (lift-ren s)) F.∘ suc) r  ≡⟨ cong (zero ∷_) (map-∘ (flip lookup (lift-ren s)) suc r) ⟩
    zero ∷ map (flip lookup (lift-ren s)) (map suc r)  ≡⟨⟩
    lift-ren r ⊚ lift-ren s                            ∎

  ⊚-asso : ∀ {m n k} (r : Ren m n) (s : Ren k m) (t : Tm n) → ren t (r ⊚ s) ≡ ren (ren t r) s
  ⊚-asso r s (var i) = cong var (sym (lookup-map _ i r))
  ⊚-asso r s (ƛ t) = begin
    ƛ (ren t (lift-ren (r ⊚ s)))               ≡⟨ cong (ƛ F.∘ ren t) (lift-dist r s) ⟩
    ƛ (ren t (lift-ren r ⊚ lift-ren s))        ≡⟨ cong ƛ (⊚-asso (lift-ren r) (lift-ren s) t) ⟩
    ƛ (ren (ren t (lift-ren r)) (lift-ren s))  ∎
  ⊚-asso r s (t · u) = trans (cong (_· ren u (r ⊚ s)) (⊚-asso r s t))
                              (cong (ren (ren t r) s ·_) (⊚-asso r s u))

  pR⊚-↑-map : ∀ {m n} (r : Ren m n) → pR ⊚ (lift-ren r) ≡ map suc r
  pR⊚-↑-map r = begin
    pR ⊚ (lift-ren r)                                 ≡⟨⟩
    map (λ i → lookup i (lift-ren r)) (map suc idF)   ≡⟨ cong (map (λ i → lookup i (lift-ren r)))
                                                               (sym $ (tabulate-∘ suc F.id)) ⟩
    map (λ i → lookup i (lift-ren r)) (tabulate suc)  ≡⟨ sym (tabulate-∘ _ suc) ⟩
    tabulate (flip lookup (zero ∷ map suc r) F.∘ suc) ≡⟨⟩
    tabulate (flip lookup (map suc r))                ≡⟨ tabulate∘lookup (map suc r) ⟩
    map suc r                                         ∎

  pR-⊚-↑ : ∀ {m n} (r : Ren m n) → r ⊚ pR ≡ pR ⊚ (lift-ren r) 
  pR-⊚-↑ r = begin
    r ⊚ pR                  ≡⟨⟩
    map (flip lookup pR) r  ≡⟨ map-cong lookup-pR r ⟩
    map suc r               ≡⟨ sym (pR⊚-↑-map r) ⟩
    pR ⊚ (lift-ren r)       ∎

  pR-↑ : ∀ {m n} (r : Ren m n) (t : Tm n) → ren (ren t r) pR ≡ ren (ren t pR) (lift-ren r)
  pR-↑ r t = trans (sym (⊚-asso r pR t))
                   (sym $ begin
                     ren (ren t pR) (lift-ren r)  ≡⟨ sym (⊚-asso pR (lift-ren r) t) ⟩
                     ren t (pR ⊚ (lift-ren r))    ≡⟨ cong (ren t) (sym $ pR-⊚-↑ r) ⟩
                     ren t (r ⊚ pR)               ∎
                   )

  ↑-∘r-dist : ∀ {m n k} (ts : Subst m n) (is : Ren k m) → ↑ (ts ∘r is) ≡ ↑ ts ∘r lift-ren is
  ↑-∘r-dist ts is = begin
    ↑ (ts ∘r is)                                             ≡⟨⟩
    q ∷ map (flip ren pR) (ts ∘r is)                         ≡⟨ cong (q ∷_) (sym $ map-∘ _ _ ts) ⟩
    q ∷ map (λ t → ren (ren t is) pR) ts                     ≡⟨ cong (q ∷_) (map-cong (pR-↑ is) ts) ⟩
    q ∷ map (λ t → ren (ren t pR) (lift-ren is)) ts          ≡⟨ cong (q ∷_) (map-∘ _ _ ts) ⟩
    q ∷ map (flip ren (lift-ren is)) (map (flip ren pR) ts)  ≡⟨⟩
    map (flip ren (lift-ren is)) (q ∷ map (flip ren pR) ts)  ≡⟨⟩
    ↑ ts ∘r lift-ren is                                      ∎

  map-lookup-pR : ∀ {m n k} (ts : Subst k m) (is : Ren m n) →
                  map (λ i → ren (lookup i ts) pR) is ≡ map (flip lookup (↑ ts)) (map suc is)
  map-lookup-pR ts is = sym $ begin
    map (flip lookup (↑ ts)) (map suc is)              ≡⟨ sym (map-∘ _ _ is) ⟩
    map (flip lookup (↑ ts) F.∘ suc) is                ≡⟨⟩
    map (λ i → lookup i (map (λ t → ren t pR) ts)) is  ≡⟨ map-cong (λ i → sym
                                                           (lookup-map (flip ren pR) i ts)) is ⟩
    map (λ i → ren (lookup i ts) pR) is                ∎

  ↑-r∘-dist : ∀ {m n k} (is : Ren m n) (ts : Subst k m) → ↑ (is r∘ ts) ≡ lift-ren is r∘ ↑ ts
  ↑-r∘-dist is ts = cong (_, var zero) (trans (sym (map-∘ _ _ is)) (map-lookup-pR ts is))

  ∘r-asso : ∀ {m n k} (ts : Subst m n) (is : Ren k m) (t : Tm n) →
            t [ ts ∘r is ] ≡ ren (t [ ts ]) is
  ∘r-asso ts is (var i) = sym $ lookup-map (flip ren is) i ts
  ∘r-asso ts is (t · u) = cong₂ _·_ (∘r-asso ts is t) (∘r-asso ts is u)
  ∘r-asso ts is (ƛ t) = trans (cong (ƛ F.∘ t [_]) (↑-∘r-dist ts is))
                              (cong ƛ (∘r-asso (↑ ts) (lift-ren is) t))

  r∘-asso : ∀ {m n k} (is : Ren m n) (ts : Subst k m) (t : Tm n) →
            t [ is r∘ ts ] ≡ (ren t is) [ ts ]
  r∘-asso is ts (var i) = sym $ lookup-map (flip lookup ts) i is
  r∘-asso is ts (t · u) = cong₂ _·_ (r∘-asso is ts t) (r∘-asso is ts u)
  r∘-asso is ts (ƛ t) = trans (cong (ƛ F.∘ t [_]) (↑-r∘-dist is ts))
                              (cong ƛ (r∘-asso (lift-ren is) (↑ ts) t))

  ∘pR-↑ : ∀ {m n} (ts : Subst m n) → ts ∘r pR ≡ pR r∘ (↑ ts)
  ∘pR-↑ ts = sym $ trans (sym (map-∘ _ _ idF)) (map-lookup-allFin _)

  ↑-dist : ∀ {m n k} (ts : Subst m n) (us : Subst k m) → ↑ (ts ∘ us) ≡ (↑ ts) ∘ (↑ us)
  ↑-dist ts us = begin
    ↑ (ts ∘ us)                                  ≡⟨⟩
    map (λ t → ren t pR) (map (_[ us ]) ts) , q  ≡⟨ cong (_, q) (sym (map-∘ _ _ ts)) ⟩
    map (λ t → ren (t [ us ]) pR) ts , q         ≡⟨ cong (_, q) (map-cong (sym F.∘ ∘r-asso us pR) ts) ⟩
    map (_[ us ∘r pR ]) ts  , q                  ≡⟨ cong (_, q) (map-cong (λ x → cong (x [_])
                                                                          (∘pR-↑ us)) ts) ⟩
    map (_[ pR r∘ (↑ us) ]) ts , q               ≡⟨ cong (_, q) (map-cong (r∘-asso _ _) ts) ⟩
    map (_[ ↑ us ] F.∘ flip ren pR) ts , q       ≡⟨ cong (_, q) (map-∘ _ _ ts) ⟩
    map (_[ ↑ us ]) (map (flip ren pR) ts) , q   ≡⟨⟩
    map (_[ ↑ us ]) (↑ ts)                       ≡⟨⟩
    (↑ ts) ∘ (↑ us)                              ∎
 
  ∘=∘₂ : ∀ {m n k} (σ : Subst m n) (ω : Subst k m) → σ ∘ ω ≡ σ ∘₂ ω
  ∘=∘₂ [] ω = refl
  ∘=∘₂ (t ∷ σ) ω = cong (λ x → _ ∷ x) (∘=∘₂ σ ω)

  var[p] : ∀ {n} (i : Fin n) → var i [ p {n} ] ≡ var (suc i)
  var[p] i = lookup-p i

  -- this lemma lives in the lemmas record for substitution
  postulate 
    renλ : ∀ {n} (t : Tm (1 + n)) → ren t (lift-ren pR) ≡ t [ ↑ p ]

  wk-[p] : ∀ {n} (t : Tm n) → weaken t ≡ t [ p {n} ]
  wk-[p] (var ι) = trans (wkVar ι) (sym $ var[p] ι)
  wk-[p] (t · u) = cong₂ _·_ (wk-[p] t) (wk-[p] u)
  wk-[p] (ƛ t)   = cong ƛ (renλ t)

  mapWk-∘p : ∀ {m n} (σ : Subst m n) → σ ∘ p ≡ weaken-subst σ
  mapWk-∘p [] = refl
  mapWk-∘p (x ∷ σ) = trans (cong (_∷ σ ∘ p) (sym $ wk-[p] x))
                           (cong (weaken x ∷_) (mapWk-∘p σ))

  p′0=[] : ∀ {m} → p′ m 0 ≡ []
  p′0=[] {zero}  = refl
  p′0=[] {suc m} = refl

  lookup-wk : ∀ {m n} (i : Fin n) (ρ : Subst m n) →
              weaken (lookup i ρ) ≡ lookup i (weaken-subst ρ)
  lookup-wk zero (x ∷ ρ) = refl
  lookup-wk (suc i) (x ∷ ρ) = lookup-wk i ρ            

