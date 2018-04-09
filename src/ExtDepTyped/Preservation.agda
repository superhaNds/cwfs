-------------------------------------------------------------------------------------------
-- A extrinsic ΠU-cwf with implicit substitutions. We add the typing rules to the raw
-- syntax.
-------------------------------------------------------------------------------------------
module ExtDepTyped.Preservation where

open import Function as F using (_$_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Vec hiding ([_] ; _∈_)
open import Data.Vec.Properties
open import Data.Vec.All as All
  using (All; All₂; []; _∷_; map₂)
open import Data.Vec.All.Properties
  using (gmap; gmap₂; gmap₂₁; gmap₂₂)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import ExtDepTyped.LambdaSLIB

-------------------------------------------------------------------------------------------
-- Type system

-- Wellscoped contexts

q : ∀ {n} → Tm (1 + n)
q = var zero

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

open TermSubst tmSubst hiding (var)

toVec : ∀ {n} → Ctx n → Vec (Tm n) n
toVec ⋄       = []
toVec (Γ ∙ A) = map weaken (toVec Γ) , weaken A

lookup' : ∀ {n} → Fin n → Ctx n → Tm n
lookup' i Γ = lookup i (toVec Γ)

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _▹_⊢_

data _⊢    : ∀ {n} (Γ : Ctx n) → Set

data _⊢_   : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Tm n) (A : Tm n) → Set

data _▹_⊢_ : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) (γ : Sub Tm n m) → Set

data _⊢ where

  c-emp : ⋄ ⊢

  c-ext : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢
          → Γ ⊢ A
          → Γ ∙ A ⊢
          
data _⊢_ where

  ty-U : ∀ {n} {Γ : Ctx n}
         → Γ ⊢
         → Γ ⊢ U         

  ty-∈U : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A ∈ U
          → Γ ⊢ A

  ty-Π-F : ∀ {n} {Γ : Ctx n} {A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ Π A B

data _⊢_∈_ where
  tm-var : ∀ {n} {i : Fin n} {Γ : Ctx n}
           → Γ ⊢
           → Γ ⊢ var i ∈ lookup' i Γ

  tm-app : ∀ {n} {Γ : Ctx n} {f t A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ f ∈ Π A B
           → Γ ⊢ t ∈ A
           → Γ ⊢ f · t ∈ B [ id , t ]
           
  tm-Π-I : ∀ {n} {Γ : Ctx n} {A B t}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ∙ A ⊢ t ∈ B
           → Γ ⊢ ƛ t ∈ Π A B

data _▹_⊢_ where

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → Γ ▹ ⋄ ⊢ []

  ⊢<,> : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A t γ}
         → Γ ▹ Δ ⊢ γ
         → Δ ⊢ A
         → Γ ⊢ t ∈ A [ γ ]
         → Γ ▹ Δ ∙ A ⊢ (γ , t)

tm-conv : ∀ {n} {Γ : Ctx n} {t A A'}
          → Γ ⊢ A'
          → Γ ⊢ t ∈ A
          → A' ≡ A
          → Γ ⊢ t ∈ A'
tm-conv _ t∈A refl = t∈A            

ty-conv : ∀ {n} {Γ : Ctx n} {A A'}
          → Γ ⊢ A'
          → A ≡ A'
          → Γ ⊢ A
ty-conv ⊢A refl = ⊢A          

open TermLemmas tmLemmas public hiding (var ; id ; weaken ; _↑)

getTy : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Tm n
getTy {A = A} _ = A

getTm : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Tm n
getTm {t = t} _ = t

dom : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ} → Γ ▹ Δ ⊢ ρ → Ctx n
dom {Γ = Γ} _ = Γ

cod : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ} → Γ ▹ Δ ⊢ ρ → Ctx m
cod {Δ = Δ} _ = Δ

wfTy-wf   : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ⊢

wfTm-wfTy : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Γ ⊢ A

wfSub-wf₁ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {γ} → Δ ▹ Γ ⊢ γ → Δ ⊢

wfSub-wf₂ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {γ} → Δ ▹ Γ ⊢ γ → Γ ⊢

wfTm-wf   : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Γ ⊢

-- can't solve --

-- goal : if Γ ▹ Δ ⊢ map var ρ and Γ ⊢ var x ∈ A [ map var ρ ], then Γ ∙ A ⊢ var (suc x) ∈ A [ map var (map suc ρ) ]
{- map-suc-pres : ∀ {m n Γ Δ A} (ρ : Sub Fin m n) →
               Γ ⊢ A →
               Γ ▹ Δ ⊢ map var ρ →
               Γ ∙ A ▹ Δ ⊢ map var (map suc ρ)
map-suc-pres [] ⊢A (⊢<> x) = ⊢<> (c-ext x ⊢A)
map-suc-pres {Γ = Γ} {A = A} (x ∷ ρ) Γ⊢A (⊢<,> ⊢ρ Δ⊢A' ∈A[]) =
    ⊢<,> (map-suc-pres ρ Γ⊢A ⊢ρ) Δ⊢A' {!!} 
  where Γ∙A⊢ = c-ext (wfTy-wf Γ⊢A) Γ⊢A -}

weaken-pr : ∀ {n} {Γ : Ctx n} {A B}
            → Γ ⊢ A
            → Γ ⊢ B
            → Γ ∙ A ⊢ weaken B
weaken-pr A B = {!!}

{- maybe needed
weaken-tm : ∀ {n} {Δ : Ctx n} {t A B}
            → Δ ⊢ A
            → Δ ⊢ t ∈ B
            → Δ ∙ A ⊢ weaken t ∈ weaken B
weaken-tm ⊢A ∈B = {!!}
-}

-- needed for ↑ and subsequently id and p
map-wk-preserv : ∀ {m n Γ Δ A} {γ : Sub Tm m n}
                   → Γ ⊢ A
                   → Γ ▹ Δ ⊢ γ
                   → Γ ∙ A ▹ Δ ⊢ map weaken γ
map-wk-preserv ⊢A  (⊢<> Γ⊢) = ⊢<> (c-ext Γ⊢ ⊢A)
map-wk-preserv ⊢A₁ (⊢<,> ⊢γ ⊢A ∈A[γ]) = ⊢<,> (map-wk-preserv ⊢A₁ ⊢γ) ⊢A {!!} -- Γ ∙ A₁ ⊢ weaken t ∈ A [ map weaken γ ]

-- goal: Γ ∙ A ⊢ var zero ∈ B [ map weaken ρ ]
↑-preserv : ∀ {m n Γ Δ A B} {ρ : Sub Tm m n}
            → Γ ⊢ A
            → Δ ⊢ B
            → Γ ▹ Δ ⊢ ρ
            → Γ ∙ A ▹ Δ ∙ B ⊢ ρ ↑
↑-preserv ⊢A ⊢B ⊢ρ = ⊢<,> (map-wk-preserv ⊢A ⊢ρ) ⊢B {!!}

-- how

toAll : ∀ {n} {Γ : Ctx n} → Γ ⊢ → All (Γ ⊢_) (toVec Γ)
toAll c-emp         = []
toAll (c-ext Γ⊢ ⊢A) = weaken-pr ⊢A ⊢A ∷ gmap (weaken-pr ⊢A) (toAll Γ⊢)

lookup-wf : ∀ {n} {Γ : Ctx n} (i : Fin n) → Γ ⊢ → Γ ⊢ lookup' i Γ
lookup-wf i Γ⊢ = All.lookup i (toAll Γ⊢)
  
varty : ∀ {n} {Γ : Ctx n} (i : Fin n) → Γ ⊢ → Γ ⊢ var i ∈ lookup' i Γ
varty () c-emp
varty _ (c-ext Γ⊢ x) = tm-var (c-ext Γ⊢ x)

wf⁻¹ : ∀ {n} {Γ : Ctx n} {A}
       → Γ ∙ A ⊢
       → Γ ⊢
wf⁻¹ (c-ext Γ⊢ _) = Γ⊢

wf⁻² : ∀ {n} {Γ : Ctx n} {A}
       → Γ ∙ A ⊢
       → Γ ⊢ A
wf⁻² (c-ext _ ⊢A) = ⊢A       

private

  lookup-map : ∀ {a b n} {A : Set a} {B : Set b}
               (i : Fin n) (f : A → B) (xs : Vec A n)
             → lookup i (map f xs) ≡ f (lookup i xs)
  lookup-map zero    f (x ∷ xs) = refl
  lookup-map (suc i) f (x ∷ xs) = lookup-map i f xs

-- unityped cwf axioms
postulate
  p∘cons : ∀ {n m} {t : Tm n} {γ : Sub Tm m n} → p ∘ (γ , t) ≡ γ 
  sub-p  : ∀ {n} {t : Tm n} → weaken t ≡ t [ p ]
  subComp : ∀ {m n k} t (γ : Sub Tm n m) (δ : Sub Tm m k) → t [ γ ∘ δ ] ≡ t [ γ ] [ δ ]

lookup-preserv : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} i {γ}
                 → Δ ▹ Γ ⊢ γ
                 → Δ ⊢ lookup i γ ∈ (lookup' i Γ [ γ ])
lookup-preserv {Γ = Γ ∙ A} {Δ} zero {t ∷ γ} (⊢<,> ⊢γ ⊢A ∈A[γ]) = lk-base ∈A[γ]
  where lk-base : Δ ⊢ t ∈ (A [ γ ]) → Δ ⊢ t ∈ (weaken A [ γ , t ])
        lk-base hyp rewrite sub-p {t = A}
                          | sym (subComp A p (γ , t)) --sym (/-⊙ {ρ₁ = p} {ρ₂ = (γ , t)} A)
                          | p∘cons {t = t} {γ = γ} = hyp
lookup-preserv {Γ = Γ ∙ A} {Δ} (suc i) {t ∷ γ} (⊢<,> ⊢γ ⊢A ∈A[γ])
      rewrite lookup-map i weaken (toVec Γ) = lk-step (lookup-preserv i ⊢γ)
  where lk-step : Δ ⊢ lookup i γ ∈ (lookup' i Γ [ γ ])
                → Δ ⊢ lookup i γ ∈ weaken (lookup' i Γ) [ γ , t ]
        lk-step hyp rewrite sub-p {t = lookup' i Γ}
                          | sym (subComp (lookup' i Γ) p (γ , t)) -- sym (/-⊙ {ρ₁ = p} {ρ₂ = (γ , t)} (lookup' i Γ))
                          | p∘cons {t = t} {γ = γ} = hyp

tm-sub : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
             {A t γ}
           → Δ ⊢ t ∈ A
           → Γ ▹ Δ ⊢ γ
           → Γ ⊢ t [ γ ] ∈ A [ γ ]
     
ty-sub : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A γ}
         → Δ ⊢ A
         → Γ ▹ Δ ⊢ γ
         → Γ ⊢ A [ γ ]

id-preserv : ∀ {n} {Γ : Ctx n}
             → Γ ⊢
             → Γ ▹ Γ ⊢ id
id-preserv {Γ = ⋄}     c-emp         = ⊢<> c-emp
id-preserv {Γ = Γ ∙ A} (c-ext Γ⊢ ⊢A) = ↑-preserv ⊢A ⊢A (id-preserv Γ⊢)

p-preserv : ∀ {n} {Γ : Ctx n} {A}
            → Γ ⊢ A
            → Γ ∙ A ▹ Γ ⊢ p
p-preserv ⊢A = map-wk-preserv ⊢A (id-preserv (wfTy-wf ⊢A))

tm-q : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Γ ∙ A ⊢ q ∈ A [ p ]
tm-q {Γ = Γ} {A} ⊢A = help (tm-var Γ∙A⊢)
  where Γ∙A⊢ = c-ext (wfTy-wf ⊢A) ⊢A
        help : (Γ ∙ A) ⊢ q ∈ weaken A → (Γ ∙ A) ⊢ q ∈ A [ p ]
        help hyp rewrite sub-p {t = A} = hyp

wfTm-wf (tm-var Γ⊢)        = Γ⊢
wfTm-wf (tm-app _ _ _ t∈A) = wfTm-wf t∈A
wfTm-wf (tm-Π-I _ _ t∈B)   = wf⁻¹ (wfTm-wf t∈B)

wfSub-wf₂ (⊢<> _)        = c-emp
wfSub-wf₂ (⊢<,> ⊢γ ⊢A _) = c-ext (wfSub-wf₂ ⊢γ) ⊢A

wfSub-wf₁ (⊢<> ⊢Δ)      = ⊢Δ
wfSub-wf₁ (⊢<,> ⊢γ _ _) = wfSub-wf₁ ⊢γ

wfTm-wfTy (tm-var {i = i} Γ⊢)  = lookup-wf i Γ⊢
wfTm-wfTy (tm-Π-I ⊢A ⊢B _)     = ty-Π-F ⊢A ⊢B
wfTm-wfTy (tm-app ⊢A ⊢B _ t∈A) = let ⊢id = id-preserv (wfTy-wf ⊢A) in
  ty-sub ⊢B (⊢<,> ⊢id ⊢A (tm-conv (ty-sub ⊢A ⊢id) t∈A (id-vanishes _))) 

wfTy-wf (ty-U Γ⊢)      = Γ⊢
wfTy-wf (ty-∈U A∈U)    = wfTm-wf A∈U
wfTy-wf (ty-Π-F Γ⊢A _) = wfTy-wf Γ⊢A


{-
ty-sub : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A γ}
         → Δ ⊢ A
         → Γ ▹ Δ ⊢ γ
         → Γ ⊢ A [ γ ]
-}

ty-sub (ty-U Δ⊢)   ⊢γ = ty-U (wfSub-wf₁ ⊢γ)
ty-sub (ty-∈U A∈U) ⊢γ = ty-∈U (tm-sub A∈U ⊢γ)
ty-sub (ty-Π-F ⊢A ⊢B) ⊢γ = ty-Π-F (ty-sub ⊢A ⊢γ) {!!} -- goal : Γ ∙ A [ γ ] ⊢ B [ γ ↑ ] (appears often)

{-
prop:

  B [ γ ↑ ] [ id , (t [ γ ]) ]
= B [ (γ ↑) ∘ (id , t [ γ ]) ]
= B [ (γ ∘ p , q) ∘ (id , t [ γ ]) ]
= B [ (γ ∘ p) ∘ (id , t [ γ ]) , q [ (id , t [ γ ]) ] ]
= B [ γ ∘ (p ∘ (id , t [ γ ])) , t [ γ ] ]
= B [ γ ∘ id , t [ γ ] ]
= B [ γ , t [ γ ] ]
= B [ id ∘ γ , t [ γ ] ]
= B [ (id , t) ∘ γ ]
= B [ id , t ] [ γ ]
-}
postulate
  prop : ∀ {m n} {γ : Sub Tm m n} {t B}
         → B [ id , t ] [ γ ] ≡ B [ γ ↑ ] [ id , (t [ γ ]) ]


{- tm-sub : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
             {A t γ}
           → Δ ⊢ t ∈ A
           → Γ ▹ Δ ⊢ γ
           → Γ ⊢ t [ γ ] ∈ A [ γ ] -}

tm-sub (tm-var {i = i} _) ⊢γ = lookup-preserv i ⊢γ
tm-sub {γ = γ} (tm-app ⊢A ⊢B ∈Π ∈A) ⊢γ
  rewrite prop {γ = γ} {t = getTm ∈A} {B = getTy ⊢B} =
    tm-app (ty-sub ⊢A ⊢γ) {!!} (tm-sub ∈Π ⊢γ) (tm-sub ∈A ⊢γ)   -- goal : Γ ∙ A [ γ ] ⊢ B [ γ ↑ ] this appears below too
tm-sub (tm-Π-I ⊢A ⊢B ∈B) ⊢γ = tm-Π-I (ty-sub ⊢A ⊢γ) {!!} {!!}  -- second goal : Γ ∙ A [ γ ] ⊢ t [ γ ↑ ] ∈ B [ γ ↑ ]   

comp-preserv : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m}
                 {Θ : Ctx k} {γ₁ γ₂}
               → Γ ▹ Θ ⊢ γ₁
               → Δ ▹ Γ ⊢ γ₂
               → Δ ▹ Θ ⊢ γ₁ ∘ γ₂
comp-preserv (⊢<> _) ⊢γ₂ = ⊢<> (wfSub-wf₁ ⊢γ₂)
comp-preserv {Δ = Δ} {Θ = Θ ∙ A} {γ₁ = t ∷ γ₁} {γ₂}
             (⊢<,> ⊢γ₁ ⊢A ∈A[γ]) ⊢γ₂ = ⊢<,> (comp-preserv ⊢γ₁ ⊢γ₂) ⊢A (h (tm-sub ∈A[γ] ⊢γ₂))
  where h : Δ ⊢ t [ γ₂ ] ∈ (A [ γ₁ ] [ γ₂ ]) → Δ ⊢ t [ γ₂ ] ∈ (A [ γ₁ ∘ γ₂ ])               
        h hyp rewrite sym (subComp A γ₁ γ₂) = hyp

