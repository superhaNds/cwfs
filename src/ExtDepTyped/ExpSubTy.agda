module ExtDepTyped.ExpSubTy where

open import Data.Nat renaming (ℕ to Nat)
open import ExtDepTyped.Raw.ExpSub
open import Data.Product renaming (proj₁ to π₁ ; proj₂ to π₂) hiding (<_,_>)

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _⊢_∈s_

data _⊢    : ∀ {n} (Γ : Ctx n) → Set

data _⊢_   : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Tm n) (A : Tm n) → Set

data _⊢_∈s_ : ∀ {m n} (Γ : Ctx n) (γ : Sub m n) (Δ : Ctx m) → Set

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
           → Δ ⊢ γ ∈s Γ
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
           → Δ ⊢ γ ∈s Γ
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
           → Γ ⊢ ƛ t ∈ Π A B

  tm-conv : ∀ {n} {Γ : Ctx n} {t A A'}
            → Γ ⊢ A'
            → Γ ⊢ t ∈ A
            → A' ~ A
            → Γ ⊢ t ∈ A'

data _⊢_∈s_ where

  ⊢id : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → Γ ⊢ id ∈s Γ

  ⊢∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m}
         {Θ : Ctx k} {γ₁ γ₂}
       → Θ ⊢ γ₁ ∈s Γ
       → Γ ⊢ γ₂ ∈s Δ
       → Θ ⊢ γ₁ ∘ γ₂ ∈s Δ
       
  ⊢p : ∀ {n} {Γ : Ctx n} {A}
       → Γ ⊢ A
       → Γ ⊢ p ∈s Γ ∙ A

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → ⋄ ⊢ <> ∈s Γ

  ⊢<,> : ∀ {m n} {Γ : Ctx n}
           {Δ : Ctx m} {A t γ}
         → Γ ⊢ γ ∈s Δ
         → Γ ⊢ A
         → Δ ⊢ t ∈ A [ γ ]
         → Γ ∙ A ⊢ < γ , t > ∈s Δ

lemma-1 : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A
          → Γ ⊢

lemma-2T : ∀ {n} {Γ : Ctx n} {A t}
          → Γ ⊢ t ∈ A
          → Γ ⊢ A

lemma-2C : ∀ {n} {Γ : Ctx n} {A t}
           → Γ ⊢ t ∈ A
           → Γ ⊢

lemma-3 : ∀ {m n} {Γ : Ctx n}
            {Δ : Ctx m} {γ}
          → Γ ⊢ γ ∈s Δ
          → Γ ⊢ × Δ ⊢

lemma-3 (⊢id Γ⊢)       = Γ⊢ , Γ⊢
lemma-3 (⊢∘ ⊢γ₁ ⊢γ₂)   = π₁ (lemma-3 ⊢γ₁) , π₂ (lemma-3 ⊢γ₂) 
lemma-3 (⊢p ⊢A)        = lemma-1 ⊢A , c-ext (lemma-1 ⊢A) ⊢A
lemma-3 (⊢<> Δ⊢)       = c-emp , Δ⊢ 
lemma-3 (⊢<,> ⊢γ ⊢A _) = c-ext (lemma-1 ⊢A) ⊢A , π₂ (lemma-3 ⊢γ)

lemma-1 (ty-U Γ⊢)     = Γ⊢
lemma-1 (ty-∈U A∈U)   = lemma-2C A∈U
lemma-1 (ty-Π-F ⊢A _) = lemma-1 ⊢A
lemma-1 (ty-sub _ ⊢γ) = π₂ (lemma-3 ⊢γ)

lemma-2C (tm-q ⊢A)          = c-ext (lemma-1 ⊢A) ⊢A
lemma-2C (tm-sub t∈A ⊢γ)    = π₂ (lemma-3 ⊢γ)
lemma-2C (tm-app _ _ _ t∈A) = lemma-2C t∈A
lemma-2C (tm-conv _ t∈A _)  = lemma-2C t∈A
lemma-2C (tm-Π-I _ _ t∈A) with lemma-2C t∈A
... | c-ext Γ⊢ _ = Γ⊢

lemma-2T (tm-q ⊢A)            = ty-sub ⊢A (⊢p ⊢A)
lemma-2T (tm-sub t∈A ⊢γ)      = ty-sub (lemma-2T t∈A) ⊢γ
lemma-2T (tm-Π-I ⊢A ⊢B _)     = ty-Π-F ⊢A ⊢B
lemma-2T (tm-app ⊢A ⊢B _ t∈A) =
  let ⊢id = ⊢id (lemma-1 ⊢A)
  in ty-sub ⊢B (⊢<,> ⊢id ⊢A
     (tm-conv (ty-sub ⊢A ⊢id) t∈A subId))
lemma-2T (tm-conv ⊢A' _ _) = ⊢A'
