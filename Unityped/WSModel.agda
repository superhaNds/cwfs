module Unityped.WSModel where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec.Properties
open import Data.Vec
  using (Vec ; [] ; _∷_ ; map ; lookup ; allFin ; tabulate ; tail ; head)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_ ; _$_)
open import Util
open import Relation.Binary.PropositionalEquality
open import Unityped.Ucwf
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

_[_] : ∀ {n m} → WellScopedTm n → Vec (WellScopedTm m) n → WellScopedTm m
t [ ts ] = sub t ts

-- comp of homs 
comp : ∀ {m n k} → Vec (WellScopedTm n) k → Vec (WellScopedTm m) n → Vec (WellScopedTm m) k
comp []   _ = []
comp (t ∷ ts) us = sub t us ∷ comp ts us

-- weakening (derived)
lift : {n : Nat} → WellScopedTm n → WellScopedTm (suc n)
lift t = rename t (↑ _)

-- p
projSub : (n : Nat) → Vec (WellScopedTm (suc n)) n
projSub = map lift ∘ idSub

-- < Δ , τ >
ext : ∀ {m n} → Vec (WellScopedTm m) n → WellScopedTm m → Vec (WellScopedTm m) (suc n)
ext ts t = t ∷ ts

-- <>
empt : ∀ {m} → Vec (WellScopedTm m) zero
empt = []

-- Proofs of ucwf axioms

------------------------------ Auxiliary lemmas -----------------------------
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

postulate subPLift : ∀ {n} t → (sub t (projSub n)) ≡ lift t
postulate tailIdp : ∀ n → tail (idSub (suc n)) ≡ projSub n
---------------------------------------------------------------------------

t[id]=t : ∀ {n} → (t : WellScopedTm n) → sub t (idSub n) ≡ t
t[id]=t (var n x) = lookupIdLemma n x

id0=[] : idSub zero ≡ empt
id0=[] = refl

compEmpty : ∀ {m n} (ts : Vec (WellScopedTm m) n) → comp empt ts ≡ empt
compEmpty _ = refl

compInSub : ∀ {m n k} (t : WellScopedTm n) (ts : Vec (WellScopedTm k) n)
          (us : Vec (WellScopedTm m) k) → sub t (comp ts us) ≡ sub (sub t ts) us
compInSub (var .0 ()) [] us
compInSub (var _ zero) (v ∷ ts) us = refl
compInSub (var _ (suc x)) (v ∷ ts) us = compInSub (var _ x) ts us

subVar0 : ∀ {m n} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) m) →
               sub (q m) (ext ts t) ≡ t
subVar0 t ts = refl

postulate p∘x∷ts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k) → comp (projSub k) (t ∷ ts) ≡ ts

{-p∘<ts,t>=ts : ∀ {n k : Nat} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) k)
                → comp (projSub k) (t ∷ ts) ≡ ts
p∘<ts,t>=ts t [] = refl
p∘<ts,t>=ts t (x ∷ ts) = begin
    comp (projSub _) (t ∷ x ∷ ts)
  ≡⟨ refl ⟩
    sub (var _ (suc zero)) (t ∷ x ∷ ts) ∷ comp (tail $ projSub _) (t ∷ x ∷ ts)
  ≡⟨ refl ⟩
    x ∷ comp (tail $ map lift (idSub (suc _))) (t ∷ x ∷ ts)
  ≡⟨ {!!} ⟩
    x ∷ ts
  ∎-}
  
compRightOfHomExt : ∀ {m n} (t : WellScopedTm n) (ts : Vec (WellScopedTm n) m)
   (us : Vec (WellScopedTm m) n) → comp (ext ts t) us ≡ ext (comp ts us) (sub t us)
compRightOfHomExt _ _ _ = refl

compLeftId : ∀ {m n : Nat} → (ts : Vec (WellScopedTm m) n) → comp (idSub n) ts ≡ ts
compLeftId [] = refl
compLeftId (x ∷ ts) =
 begin
    comp (idSub _) (x ∷ ts)
  ≡⟨ refl ⟩
    (sub (head (idSub _)) (x ∷ ts)) ∷ comp (tail (idSub _)) (x ∷ ts)
  ≡⟨ refl ⟩
     (sub (q _) (x ∷ ts)) ∷ comp (tail (idSub _)) (x ∷ ts)  
  ≡⟨ cong (λ a → (sub (q _) (x ∷ ts)) ∷ comp a (x ∷ ts)) (tailIdp _) ⟩
    (sub (q _) (x ∷ ts)) ∷ comp (projSub _) (x ∷ ts) 
  ≡⟨ cong (λ a → (sub (q _) (x ∷ ts)) ∷ a) (p∘x∷ts x ts) ⟩
    (sub (q _) (x ∷ ts)) ∷ ts
  ≡⟨ refl ⟩
    x ∷ ts
  ∎

compRightId : ∀ {m n : Nat} → (ts : Vec (WellScopedTm m) n) → comp ts (idSub m)  ≡ ts
compRightId [] = refl
compRightId (x ∷ ts) rewrite t[id]=t x | compRightId ts = refl

compAssoc : ∀ {m n k p} (ts : Vec (WellScopedTm n) k) (us : Vec (WellScopedTm m) n)
    (vs : Vec (WellScopedTm p) m) → comp (comp ts us) vs ≡ comp ts (comp us vs)
compAssoc [] us vs = refl
compAssoc (x ∷ ts) us vs = sym $
  begin
    sub x (comp us vs) ∷ comp ts (comp us vs)
  ≡⟨ cong (λ d → d ∷ comp ts (comp us vs)) (compInSub x us vs) ⟩
    sub (sub x us) vs ∷ comp ts (comp us vs)
  ≡⟨ sym (cong (_∷_ (sub (sub x us) vs)) (compAssoc ts us vs)) ⟩
    sub (sub x us) vs ∷ comp (comp ts us) vs
  ∎
  
id=<p,q> : ∀ (n : Nat) → idSub (suc n) ≡ q n ∷ (projSub n)
id=<p,q> zero = refl
id=<p,q> (suc n) = cong (_∷_ (q _)) (tailIdp (suc n))

wellscopedTermsAsUcwf : Ucwf (WellScopedTm)
wellscopedTermsAsUcwf = record
                          { id = idSub
                          ; <> = λ _ → empt
                          ; p = projSub
                          ; q = q
                          ; _,_,_⟨_∘_⟩ = λ μ ν k t v → comp t v
                          ; _,_▹_[_] = λ μ ν t ts → sub t ts
                          ; _,_<_,_> = λ μ ν xs x → ext xs x
                          ; id₀ = id0=[]
                          ; ∘<> = compEmpty
                          ; id<p,q> = id=<p,q> _
                          ; ∘lid = compLeftId
                          ; ∘rid = compRightId
                          ; ∘asso = compAssoc
                          ; subid = t[id]=t
                          ; p∘<γ,α> = p∘x∷ts
                          ; q[<γ,α>] = subVar0
                          ; ∘sub = compInSub
                          ; <δ,α>∘γ = compRightOfHomExt
                          }
