module Unityped.WSModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec.Properties
open import Data.Vec
  using (Vec ; [] ; _∷_ ; map ; lookup ; allFin ; tabulate ; tail ; head)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_)
open import Util
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data WellScopedTm : Nat → Set where
  var : (n : Nat) → Fin n → WellScopedTm n

id : (n : Nat) → Vec (Fin n) n
id = allFin

↑_ : ∀ n → Vec (Fin (suc n)) n
↑ _ = tabulate suc

rename : ∀ {n m} (t : WellScopedTm n) (is : Vec (Fin m) n) → WellScopedTm m
rename {_} {m}(var _ i) is = var m (lookup i is)

-- Corresponding Ucwf terms --

-- q
q : (n : Nat) → WellScopedTm (suc n)
q n = var (suc n) zero

-- id
idSub : ∀ n → Vec (WellScopedTm n) n
idSub n = tabulate (var n)

-- sub
sub : ∀ {n m} → WellScopedTm n → Vec (WellScopedTm m) n → WellScopedTm m
sub (var _ x) ts = lookup x ts

-- comp of homs 
comp : ∀ {m n k} → Vec (WellScopedTm n) k → Vec (WellScopedTm m) n → Vec (WellScopedTm m) k
comp []   _ = []
comp (t ∷ ts) us = sub t us ∷ comp ts us

--sub t vmn ∷ (comp vmn vnk)
-- weakening (derived)
lift : {n : Nat} → WellScopedTm n → WellScopedTm (suc n)
lift {n} t = rename t (↑ n)

-- p
projSub : (n : Nat) → Vec (WellScopedTm (suc n)) n
projSub = map lift ∘ idSub

-- < Δ , τ >
ext : ∀ {m n} → Vec (WellScopedTm m) n → WellScopedTm m → Vec (WellScopedTm m) (suc n)
ext ts t = t ∷ ts

-- <>
empt : ∀ {m} → Vec (WellScopedTm m) zero
empt = []

-- Proofs

liftVar : ∀ n i → lift (var n i) ≡ var (suc n) (suc i)
liftVar n i = cong (var (suc n)) (lookup∘tabulate suc i)

lookupIdLemma : ∀ n i → lookup i (idSub n) ≡ var n i
lookupIdLemma n i = lookup∘tabulate (var n) i

lookupPLemma : ∀ n i → lookup i (projSub n) ≡ var (suc n) (suc i)
lookupPLemma n i =
  begin
    lookup i (projSub n)
  ≡⟨ refl ⟩
    lookup i (map lift (idSub n))
  ≡⟨ sym (lookupMap n i (idSub n)) ⟩
    lift (lookup i (idSub n))
  ≡⟨ cong lift (lookupIdLemma n i) ⟩
    lift (var n i)
  ≡⟨ liftVar n i ⟩
    var (suc n) (suc i)
  ∎

t[id]=t : ∀ {n} → (t : WellScopedTm n) → sub t (idSub n) ≡ t
t[id]=t (var n x) = lookupIdLemma n x

id0=[] : idSub zero ≡ empt
id0=[] = refl

postulate tailIdp : ∀ n → tail (idSub (suc n)) ≡ projSub n
-- tailIdp zero = refl
-- tailIdp (suc n) = {!!}

id<p,q> : ∀ (n : Nat) → idSub (suc n) ≡ q n ∷ (projSub n)
id<p,q> zero = refl
id<p,q> (suc n) =
  begin
    idSub (suc (suc n))
  ≡⟨ refl ⟩
    var _ zero ∷ (tail (idSub _))
  ≡⟨ refl ⟩
    q _ ∷ tail (idSub _)
  ≡⟨ cong (λ x → q _ ∷ x) (tailIdp (suc n)) ⟩
    q _ ∷ projSub _
  ∎

v∘rid : ∀ {m n : Nat} → (ts : Vec (WellScopedTm m) n) → comp ts (idSub m)  ≡ ts
v∘rid [] = refl
v∘rid (x ∷ ts) rewrite t[id]=t x | v∘rid ts = refl

postulate p∘x∷ts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k) → comp (projSub k) (t ∷ ts) ≡ ts
-- p∘x∷ts t [] = refl
-- p∘x∷ts x (t ∷ ts) = 

v∘lid : ∀ {m n : Nat} → (ts : Vec (WellScopedTm m) n) → comp (idSub n) ts ≡ ts
v∘lid [] = refl
v∘lid (x ∷ ts) =
 begin
    comp (idSub _) (x ∷ ts)
  ≡⟨ refl ⟩
    (sub (head (idSub _)) (x ∷ ts)) ∷ comp (tail (idSub _)) (x ∷ ts)
  ≡⟨ refl ⟩
     (sub (var _ zero) (x ∷ ts)) ∷ comp (tail (idSub _)) (x ∷ ts)  
  ≡⟨ cong (λ a → (sub (var _ zero) (x ∷ ts)) ∷ comp a (x ∷ ts)) (tailIdp _) ⟩
    (sub (var _ zero) (x ∷ ts)) ∷ comp (projSub _) (x ∷ ts) 
  ≡⟨ cong (λ a → (sub (var _ zero) (x ∷ ts)) ∷ a) (p∘x∷ts x ts) ⟩
    (sub (var _ zero) (x ∷ ts)) ∷ ts
  ≡⟨ refl ⟩
    x ∷ ts
  ∎

