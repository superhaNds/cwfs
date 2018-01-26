module CwfObj where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Product renaming (proj₁ to π₁ ; proj₂ to π₂) hiding (<_,_>)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR

data Ctx : Nat → Set
data Tm  : Nat → Set
data Sub : Nat → Nat → Set

data Ctx where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

-- Raw terms and type formers

data Tm where
  q    : ∀ {n} → Tm (1 + n)
  _[_] : ∀ {m n} → Tm n → Sub m n → Tm m
  lam  : ∀ {n} → Tm (1 + n) → Tm n
  app  : ∀ {n} → Tm n → Tm n → Tm n
  Π    : ∀ {n} → Tm n → Tm (1 + n) → Tm n
  U    : ∀ {n} → Tm n

infix 8 _∘_

-- Raw morphisms

data Sub where
  id    : ∀ {n} → Sub n n
  _∘_   : ∀ {m n k} → Sub n k → Sub m n → Sub m k
  p     : ∀ {n} → Sub (1 + n) n
  <>    : ∀ {m} → Sub m 0
  <_,_> : ∀ {m n} → Sub m n → Tm m → Sub m (1 + n)

⇑_ : ∀ {m n} → Sub m n → Sub (1 + m) (1 + n)
⇑ γ = < γ ∘ p , q >

wkn : ∀ {n} → Tm n → Tm (1 + n)
wkn = _[ p ]

infix 4 _≈_
infix 4 _≋_

data _≈_ : ∀ {n} (t t' : Tm n) → Set
data _≋_ : ∀ {m n} (γ γ' : Sub m n) → Set

-- Term equality

data _≈_ where
  subId    : ∀ {n} (t : Tm n) → t [ id ] ≈ t
  qExt     : ∀ {n m} t (γ : Sub n m) → q [ < γ , t > ] ≈ t
  subComp  : ∀ {m n k} t (γ : Sub k n) (σ : Sub m k) →
             t [ γ ∘ σ ] ≈ (t [ γ ])[ σ ]
  subApp   : ∀ {n m} (γ : Sub m n) t u →
             app (t [ γ ]) (u [ γ ]) ≈ app t u [ γ ]           
  subLam   : ∀ {n m} (t : Tm (suc n)) (γ : Sub m n) →
             lam t [ γ ] ≈ lam (t [ < γ ∘ p , q > ])
  subΠ     : ∀ {n m} (γ : Sub m n) A B →
             (Π A B) [ γ ] ≈ Π (A [ γ ]) (B [ < γ ∘ p , q > ])
  subU     : ∀ {n m} {γ : Sub m n} → U [ γ ] ≈ U             
  beta     : ∀ {n} (t : Tm (suc n)) (u : Tm n) →
             app (lam t) u ≈ t [ < id , u > ]     
  sym≈     : ∀ {n} {u u′ : Tm n} → u ≈ u′ → u′ ≈ u
  trans≈   : ∀ {m} {t u v : Tm m} →
             t ≈ u → u ≈ v → t ≈ v
  cong-app : ∀ {n} {t u t′ u′ : Tm n} →
             t ≈ t′ → u ≈ u′ → app t u ≈ app t′ u′
  cong-sub : ∀ {m n} {γ σ : Sub m n} {t u} →
             t ≈ u → γ ≋ σ →
             t [ γ ] ≈ u [ σ ]
  cong-lam : ∀ {n} {t u : Tm (1 + n)} →
             t ≈ u → lam t ≈ lam u

refl≈ : ∀ {n} {t : Tm n} → t ≈ t
refl≈ {t = t} = trans≈ (sym≈ (subId t)) (subId t)

-- Substitution equality

data _≋_ where
  id₀      : id {0} ≋ <>
  <>Lzero  : ∀ {m n} (γ : Sub m n) → <> ∘ γ ≋ <>
  extId    : ∀ {n} → id {1 + n} ≋ < p , q >
  idL      : ∀ {m n} (γ : Sub m n) → id ∘ γ ≋ γ
  idR      : ∀ {m n} (γ : Sub m n) → γ ∘ id ≋ γ
  assoc    : ∀ {m n k p} (γ : Sub n k) (σ : Sub m n) (τ : Sub p m) →
             (γ ∘ σ) ∘ τ  ≋ γ ∘ (σ ∘ τ) 
  pExt     : ∀ {m n} u (σ : Sub m n) → σ ≋ p ∘ < σ , u >           
  maps     : ∀ {m n k} t (γ : Sub n k) (σ : Sub m n) →
             < γ , t > ∘ σ  ≋ < γ ∘ σ , t [ σ ] > 
  sym≋     : ∀ {m n} {γ σ : Sub m n} → γ ≋ σ → σ ≋ γ
  trans≋   : ∀ {m n} {γ σ τ : Sub m n} →
             γ ≋ σ → σ ≋ τ → γ ≋ τ
  cong-<,> : ∀ {m n} {γ σ : Sub m n} {t u} →
             t ≈ u → γ ≋ σ →
             < γ , t > ≋ < σ , u >
  cong-∘   : ∀ {m n k} {γ τ : Sub n k} {σ ξ : Sub m n} →
             γ ≋ τ → σ ≋ ξ →
             γ ∘ σ ≋ τ ∘ ξ

refl≋ : ∀ {m n} {γ : Sub m n} → γ ≋ γ
refl≋ {γ = γ} = trans≋ (sym≋ (idL γ)) (idL γ)

TmSetoid : ∀ {n} → Setoid _ _
TmSetoid {n} =
  record { Carrier = Tm n
         ; _≈_ = _≈_
         ; isEquivalence =
             record { refl  = refl≈
                    ; sym   = sym≈
                    ; trans = trans≈ } }

SubSetoid : ∀ {m n} → Setoid _ _
SubSetoid {m} {n} =
  record { Carrier = Sub m n
         ; _≈_ = _≋_
         ; isEquivalence =
             record { refl  = refl≋
                    ; sym   = sym≋
                    ; trans = trans≋ } }

-- There is a terminal arrow from any m to 0

ter-arrow : ∀ {m} (γ : Sub m 0) → γ ≋ <>
ter-arrow γ = begin
  γ           ≈⟨ sym≋ (idL γ) ⟩
  id {0} ∘ γ  ≈⟨ cong-∘ id₀ refl≋ ⟩
  <> ∘ γ      ≈⟨ <>Lzero γ ⟩
  <>          ∎
              where open EqR (SubSetoid {_} {_})

-- surjective pairing

surj-<,> : ∀ {m n} (γ : Sub m (1 + n)) → γ ≋ < p ∘ γ , q [ γ ] >
surj-<,> {n = n} γ = begin
  γ                    ≈⟨ sym≋ (idL γ) ⟩
  id {1 + n} ∘ γ       ≈⟨ cong-∘ extId refl≋ ⟩
  < p , q > ∘ γ        ≈⟨ maps q p γ ⟩
  < p ∘ γ , q [ γ ] >  ∎
                       where open EqR (SubSetoid {_} {_})

-- lifting a substitution distributes over composition

⇑-dist : ∀ {m n k} (γ : Sub m n) (γ' : Sub k m) → ⇑ γ ∘ ⇑ γ' ≋ ⇑ (γ ∘ γ')
⇑-dist γ γ' = begin
  ⇑ γ ∘ ⇑ γ'                                           ≈⟨ refl≋ ⟩
  < γ ∘ p , q > ∘ < γ' ∘ p , q >                       ≈⟨ maps q (γ ∘ p) < γ' ∘ p , q > ⟩
  < (γ ∘ p) ∘ < γ' ∘ p , q > , q [ < γ' ∘ p , q > ] >  ≈⟨ cong-<,> (qExt q (γ' ∘ p)) refl≋ ⟩
  < (γ ∘ p) ∘ < γ' ∘ p , q > , q >                     ≈⟨ cong-<,> refl≈ (assoc γ p < γ' ∘ p , q >) ⟩
  < γ ∘ (p ∘ < γ' ∘ p , q >) , q >                     ≈⟨ cong-<,> refl≈ (cong-∘ refl≋ (sym≋ (pExt q (γ' ∘ p)))) ⟩
  < γ ∘ (γ' ∘ p) , q >                                 ≈⟨ cong-<,> refl≈ (sym≋ (assoc γ γ' p)) ⟩
  ⇑ (γ ∘ γ')                                           ∎
                                                       where open EqR (SubSetoid {_} {_})

infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _▹_⊢_

data _⊢    : ∀ {n} (Γ : Ctx n) → Set

data _⊢_   : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (t : Tm n) (A : Tm n) → Set

data _▹_⊢_ : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) (γ : Sub m n) → Set

data _⊢ where

 c-emp : ⋄ ⊢
  
 c-ext : ∀ {n} {Γ : Ctx n} {A}
         → Γ ⊢
         → Γ ⊢ A
         → (Γ ∙ A) ⊢

data _⊢_ where

  ty-U : ∀ {n} {Γ : Ctx n}
         → Γ ⊢
         → Γ ⊢ U         

  ty-w : ∀ {n} {Γ : Ctx n} {A}
         → Γ ⊢
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
            → Γ ⊢ t ∈ A
            → A ≈ A'
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

lemma-1 : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A
          → Γ ⊢

lemma-2 : ∀ {n} {Γ : Ctx n} {A t}
          → Γ ⊢ t ∈ A
          → Γ ⊢ A

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
lemma-1 (ty-w Γ⊢ A∈U) = Γ⊢   -- lemma-1 (lemma-2 A∈U)
lemma-1 (ty-Π-F ⊢A _) = lemma-1 ⊢A
lemma-1 (ty-sub _ ⊢γ) = π₂ (lemma-3 ⊢γ)

lemma-2 (tm-q ⊢A)            = ty-sub ⊢A (⊢p ⊢A)
lemma-2 (tm-sub t∈A ⊢γ)      = ty-sub (lemma-2 t∈A) ⊢γ
lemma-2 (tm-Π-I ⊢A ⊢B _)     = ty-Π-F ⊢A ⊢B
lemma-2 (tm-app ⊢A ⊢B _ t∈A) =
  let ⊢Γ = lemma-1 ⊢A
  in ty-sub ⊢B (⊢<,> (⊢id ⊢Γ) ⊢A (tm-conv t∈A (sym≈ (subId _))))
lemma-2 (tm-conv t∈A' A'≈A) = {!!}                                              
