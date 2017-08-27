module _ where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Ucfw2 : Set₁ where
  field
    Ctx   : Set
    Hom   : Ctx → Ctx → Set
    id    : (n : Ctx) → Hom n n
    comp  : (m n l : Ctx) → Hom n l → Hom m n → Hom m l
    Ø     : Ctx
    <>    : (m : Ctx) → Hom m Ø
    suc′  : Ctx → Ctx
    <_,_> : (m n : Ctx) → Hom m n → Hom m (suc′ Ø) → Hom m (suc′ n)
    p     : (n : Ctx) → Hom (suc′ n) n
    q     : (n : Ctx) → Hom (suc′ n) (suc′ Ø)

    
    ε     : ∀ {m n : Ctx} (ts : Hom m n) → comp m n Ø (<> n) ts ≡ <> m
    lid   : ∀ {m n : Ctx} (ts : Hom m n) → comp m n n (id n) ts ≡ ts
    rid   : ∀ {m n : Ctx} (ts : Hom m n) → comp m m n ts (id m) ≡ ts
    asso  : ∀ {m n k : Ctx} (ts : Hom n k) (us : Hom m n) (vs : Hom m m)
              → comp m m k (comp m n k ts us) vs ≡ comp m n k ts (comp m m n us vs)
    
