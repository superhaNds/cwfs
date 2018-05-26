module ExtDepTyped.Raw.ExpSub where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product renaming (proj₁ to π₁ ; proj₂ to π₂) hiding (<_,_>)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR

data Tm : Nat → Set
data Sub : Nat → Nat → Set

infix 8 _∘_

data Tm where
  q    : ∀ {n} → Tm (suc n)
  _[_] : ∀ {m n} → Tm n → Sub m n → Tm m
  app  : ∀ {n} → Tm n → Tm n → Tm n
  ƛ    : ∀ {n} → Tm (suc n) → Tm n
  Π    : ∀ {n} → Tm n → Tm (1 + n) → Tm n
  U    : ∀ {n} → Tm n

data Sub where
  id    : ∀ {n} → Sub n n
  _∘_   : ∀ {m n k} → Sub m n → Sub k m → Sub k n
  p     : ∀ {n} → Sub (suc n) n
  <>    : ∀ {n} → Sub n 0
  <_,_> : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)

infix 4 _~_
infix 4 _≈_

⇑_ : ∀ {m n} → Sub m n → Sub (1 + m) (1 + n)
⇑ γ = < γ ∘ p , q >

data _~_ : {n : Nat} → Tm n → Tm n → Set
data _≈_ : {m n : Nat} → Sub m n → Sub m n → Set

data _~_ where
  q-sub : ∀ {m n} {γ : Sub m n} {t} → q [ < γ , t > ] ~ t

  subId : ∀ {n} {t : Tm n} → t [ id ] ~ t

  subComp : ∀ {m n k} {t} {γ : Sub m n} {δ : Sub k m}
            → t [ γ ∘ δ ] ~ t [ γ ] [ δ ]

  subApp : ∀ {m n} {f t} {δ : Sub m n}
           → (app f t) [ δ ] ~ app (f [ δ ]) (t [ δ ])

  subLam : ∀ {m n} {t} {δ : Sub m n}
           → (ƛ t) [ δ ] ~ ƛ (t [ < δ ∘ p , q > ])
            
  subΠ : ∀ {n m} (γ : Sub m n) A B
         → (Π A B) [ γ ] ~ Π (A [ γ ]) (B [ ⇑ γ ])

  β : ∀ {n} {t : Tm (suc n)} {u} → app (ƛ t) u ~ t [ < id , u > ]

  η : ∀ {n} {t : Tm n} → ƛ (app (t [ p ]) q) ~ t

  cong-sub : ∀ {m n} {γ δ : Sub m n} {t u}
             → t ~ u
             → γ ≈ δ
             → t [ γ ] ~ u [ δ ]

  cong-app : ∀ {n} {t t' u u' : Tm n}
             → t ~ t'
             → u ~ u'
             → app t u ~ app t' u'

  cong-lam : ∀ {n} {t t' : Tm (suc n)}
             → t ~ t'
             → ƛ t ~ ƛ t'

  cong-Π : ∀ {n} {A A' : Tm n} {B B'}
           → A ~ A'
           → B ~ B'
           → Π A B ~ Π A' B'

  sym~ : ∀ {n} {t₁ t₂ : Tm n}
         → t₁ ~ t₂
         → t₂ ~ t₁

  trans~ : ∀ {n} {t₁ t₂ t₃ : Tm n}
           → t₁ ~ t₂
           → t₂ ~ t₃
           → t₁ ~ t₃

refl~ : ∀ {n} {t : Tm n} → t ~ t
refl~ = trans~ (sym~ subId) subId

data _≈_ where
  left-zero : ∀ {n m} {γ : Sub n m} → <> ∘ γ ≈ <>

  id-zero : id {0} ≈ <>

  idL : ∀ {m n} {γ : Sub m n} → id ∘ γ ≈ γ

  idR : ∀ {m n} {γ : Sub m n} → γ ∘ id ≈ γ

  ∘-asso : ∀ {m n k j} {γ₁ : Sub n k} {γ₂ : Sub m n} {γ₃ : Sub j m}
           → (γ₁ ∘ γ₂) ∘ γ₃ ≈ γ₁ ∘ (γ₂ ∘ γ₃)

  p-∘ : ∀ {m n} {γ : Sub m n} {t} → p ∘ < γ , t > ≈ γ

  idExt : ∀ {n} → id {1 + n} ≈ < p , q >

  compExt : ∀ {m n k} {δ : Sub n m} {γ : Sub k n} {t}
            → < δ , t > ∘ γ ≈ < δ ∘ γ , t [ γ ] >

  cong-<,> : ∀ {m n} {δ γ : Sub m n} {t u}
             → t ~ u
             → δ ≈ γ
             → < δ , t > ≈ < γ , u >

  cong-∘ : ∀ {m n k} {δ₁ δ₂ : Sub n k} {γ₁ γ₂ : Sub m n}
           → δ₁ ≈ δ₂
           → γ₁ ≈ γ₂
           → δ₁ ∘ γ₁ ≈ δ₂ ∘ γ₂

  sym≈ : ∀ {m n} {γ₁ γ₂ : Sub m n}
         → γ₁ ≈ γ₂
         → γ₂ ≈ γ₁

  trans≈ : ∀ {m n} {γ₁ γ₂ γ₃ : Sub m n}
           → γ₁ ≈ γ₂
           → γ₂ ≈ γ₃
           → γ₁ ≈ γ₃

refl≈ : ∀ {m n} {γ : Sub m n} → γ ≈ γ
refl≈ = trans≈ (sym≈ idL) idL

cong-sub₁ : ∀ {m n} {γ : Sub m n} {t u} → t ~ u → t [ γ ] ~ u [ γ ]
cong-sub₁ t~u = cong-sub t~u refl≈

cong-sub₂ : ∀ {m n} {γ δ : Sub m n} {t} → γ ≈ δ → t [ γ ] ~ t [ δ ]
cong-sub₂ γ≈δ = cong-sub refl~ γ≈δ

cong-<, : ∀ {m n} {γ δ : Sub m n} {t} → γ ≈ δ → < γ , t > ≈ < δ , t >
cong-<, γ≈δ = cong-<,> refl~ γ≈δ

cong-,> : ∀ {m n} {γ : Sub m n} {t u} → t ~ u → < γ , t > ≈ < γ , u >
cong-,> t~u = cong-<,> t~u refl≈

cong-∘₁ : ∀ {m n k} {γ γ' : Sub n k} {δ : Sub m n}
          → γ ≈ γ' → γ ∘ δ ≈ γ' ∘ δ
cong-∘₁ γ≈δ = cong-∘ γ≈δ refl≈

cong-∘₂ : ∀ {m n k} {γ : Sub n k} {δ δ' : Sub m n}
          → δ ≈ δ' → γ ∘ δ ≈ γ ∘ δ'
cong-∘₂ δ≈δ = cong-∘ refl≈ δ≈δ

cong-appl : ∀ {n} {f g t : Tm n} → f ~ g → app f t ~ app g t
cong-appl f~g = cong-app f~g refl~

cong-appr : ∀ {n} {f t u : Tm n} → t ~ u → app f t ~ app f u
cong-appr t~u = cong-app refl~ t~u

TmSetoid : ∀ {n} → Setoid _ _
TmSetoid {n} =
  record { Carrier = Tm n
         ; _≈_ = _~_
         ; isEquivalence =
             record { refl  = refl~
                    ; sym   = sym~
                    ; trans = trans~ } }

SubSetoid : ∀ {m n} → Setoid _ _
SubSetoid {m} {n} =
  record { Carrier = Sub m n
         ; _≈_ = _≈_
         ; isEquivalence =
             record { refl  = refl≈
                    ; sym   = sym≈
                    ; trans = trans≈ } }


emptySub : ∀ {n} (γ : Sub n zero) → γ ≈ <>
emptySub γ = begin
  γ           ≈⟨ sym≈ idL ⟩
  id {0} ∘ γ  ≈⟨ cong-∘₁ id-zero ⟩
  <> ∘ γ      ≈⟨ left-zero ⟩ 
  <>
  ∎
  where open EqR (SubSetoid {_} {_})

surj-<,> : ∀ {n m} (γ : Sub m (suc n)) → γ ≈ < p ∘ γ , q [ γ ] >
surj-<,> γ = begin
  γ                    ≈⟨ sym≈ idL ⟩
  id ∘ γ               ≈⟨ cong-∘₁ idExt  ⟩
  < p , q > ∘ γ        ≈⟨ compExt ⟩
  < p ∘ γ , q [ γ ] >
  ∎
  where open EqR (SubSetoid {_} {_})

-----------------------------------------------------------------------------------------------
-- A few theorems based on the raw axiomatization

-- there is a unique terminal arrow for any object with codomain 0

ter-arrow : ∀ {m} (γ : Sub m 0) → γ ≈ <>
ter-arrow γ = begin
  γ           ≈⟨ sym≈ idL ⟩
  id {0} ∘ γ  ≈⟨ cong-∘₁ id-zero ⟩
  <> ∘ γ      ≈⟨ left-zero ⟩
  <>
  ∎
  where open EqR (SubSetoid {_} {_})

-- lifting and extending a substitution distributes over composition

⇑-dist : ∀ {m n k} (γ : Sub m n) (γ' : Sub k m) → ⇑ γ ∘ ⇑ γ' ≈ ⇑ (γ ∘ γ')
⇑-dist γ γ' = begin
  ⇑ γ ∘ ⇑ γ'                                           ≈⟨ refl≈ ⟩
  < γ ∘ p , q > ∘ < γ' ∘ p , q >                       ≈⟨ compExt ⟩
  < (γ ∘ p) ∘ < γ' ∘ p , q > , q [ < γ' ∘ p , q > ] >  ≈⟨ cong-,> q-sub ⟩
  < (γ ∘ p) ∘ < γ' ∘ p , q > , q >                     ≈⟨ cong-<, ∘-asso ⟩
  < γ ∘ (p ∘ < γ' ∘ p , q >) , q >                     ≈⟨ cong-<, (cong-∘₂ p-∘) ⟩
  < γ ∘ (γ' ∘ p) , q >                                 ≈⟨ cong-<, (sym≈ ∘-asso) ⟩
  ⇑ (γ ∘ γ')
  ∎
  where open EqR (SubSetoid {_} {_})

data Ctx : Nat → Set
data Ctx where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

{-
infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _▹_⊢_

-- Well-formed context

data _⊢    : ∀ {n} (Γ : Ctx n) → Set

-- Well-formed type

data _⊢_   : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

-- Well-formed term

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Tm n) (A : Tm n) → Set

-- Well-formed substitution

data _▹_⊢_ : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) (γ : Sub m n) → Set

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

  ty-sub : ∀ {m n} {Δ : Ctx m}
             {Γ : Ctx n} {A γ}
           → Δ ⊢ A
           → Γ ▹ Δ ⊢ γ
           → Γ ⊢ A [ γ ]

  ty-Π-F : ∀ {n} {Γ : Ctx n} {A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ Π A B

data _⊢_∈_ where

  tm-q : ∀ {n} {Γ : Ctx n} {A}
         → Γ ⊢ A
         → Γ ∙ A ⊢ q ∈ A [ p ]

  tm-sub : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
             {A t γ}
           → Δ ⊢ t ∈ A
           → Γ ▹ Δ ⊢ γ
           → Γ ⊢ t [ γ ] ∈ A [ γ ]

  tm-app : ∀ {n} {Γ : Ctx n} {f t A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ f ∈ Π A B
           → Γ ⊢ t ∈ A
           → Γ ⊢ app f t ∈ B [ < id , t > ]
           
  tm-Π-I : ∀ {n} {Γ : Ctx n}
             {A B t}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ∙ A ⊢ t ∈ B
           → Γ ⊢ lam t ∈ Π A B

  tm-conv : ∀ {n} {Γ : Ctx n} {t A A'}
            → Γ ⊢ A'
            → Γ ⊢ t ∈ A
            → A' ≈ A
            → Γ ⊢ t ∈ A'

data _▹_⊢_ where

  ⊢id : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → Γ ▹ Γ ⊢ id

  ⊢∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m}
         {Θ : Ctx k} {γ₁ γ₂}
       → Γ ▹ Θ ⊢ γ₁
       → Δ ▹ Γ ⊢ γ₂
       → Δ ▹ Θ ⊢ γ₁ ∘ γ₂
       
  ⊢p : ∀ {n} {Γ : Ctx n} {A}
       → Γ ⊢ A
       → Γ ∙ A ▹ Γ ⊢ p

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → Γ ▹ ⋄ ⊢ <>

  ⊢<,> : ∀ {m n} {Γ : Ctx n}
           {Δ : Ctx m} {A t γ}
         → Γ ▹ Δ ⊢ γ
         → Δ ⊢ A
         → Γ ⊢ t ∈ A [ γ ]
         → Γ ▹ Δ ∙ A ⊢ < γ , t >

-- Basic properties


-- Given a well-formed type in some context, the context must be well-formed

lemma-1 : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A
          → Γ ⊢

-- Given a well-formed term of some type, the type must be well-formed

lemma-2 : ∀ {n} {Γ : Ctx n} {A t}
          → Γ ⊢ t ∈ A
          → Γ ⊢ A

-- And the context

lemma-2B : ∀ {n} {Γ : Ctx n} {A t}
           → Γ ⊢ t ∈ A
           → Γ ⊢
           
-- Given a well-formed substitution between two contexts, the contexts must be well-formed

lemma-3 : ∀ {m n} {Γ : Ctx n}
            {Δ : Ctx m} {γ}
          → Δ ▹ Γ ⊢ γ
          → Γ ⊢ × Δ ⊢

lemma-3 (⊢id Γ⊢)       = Γ⊢ , Γ⊢
lemma-3 (⊢∘ ⊢γ₁ ⊢γ₂)   = π₁ (lemma-3 ⊢γ₁) , π₂ (lemma-3 ⊢γ₂) 
lemma-3 (⊢p ⊢A)        = lemma-1 ⊢A , c-ext (lemma-1 ⊢A) ⊢A
lemma-3 (⊢<> Δ⊢)       = c-emp , Δ⊢ 
lemma-3 (⊢<,> ⊢γ ⊢A _) = c-ext (lemma-1 ⊢A) ⊢A , π₂ (lemma-3 ⊢γ)

lemma-1 (ty-U Γ⊢)     = Γ⊢
lemma-1 (ty-∈U A∈U)   = lemma-2B A∈U
lemma-1 (ty-Π-F ⊢A _) = lemma-1 ⊢A
lemma-1 (ty-sub _ ⊢γ) = π₂ (lemma-3 ⊢γ)

lemma-2B (tm-q ⊢A)          = c-ext (lemma-1 ⊢A) ⊢A
lemma-2B (tm-sub t∈A ⊢γ)    = π₂ (lemma-3 ⊢γ)
lemma-2B (tm-app _ _ _ t∈A) = lemma-2B t∈A
lemma-2B (tm-conv x t∈A x₁) = lemma-2B t∈A
lemma-2B (tm-Π-I _ _ t∈A) with lemma-2B t∈A
... | c-ext Γ⊢ _ = Γ⊢

lemma-2 (tm-q ⊢A)            = ty-sub ⊢A (⊢p ⊢A)
lemma-2 (tm-sub t∈A ⊢γ)      = ty-sub (lemma-2 t∈A) ⊢γ
lemma-2 (tm-Π-I ⊢A ⊢B _)     = ty-Π-F ⊢A ⊢B
lemma-2 (tm-app ⊢A ⊢B _ t∈A) =
  let ⊢id = ⊢id (lemma-1 ⊢A)
  in ty-sub ⊢B (⊢<,> ⊢id ⊢A
     (tm-conv (ty-sub ⊢A ⊢id) t∈A (subId _)))
lemma-2 (tm-conv ⊢A' _ _) = ⊢A'
-}
