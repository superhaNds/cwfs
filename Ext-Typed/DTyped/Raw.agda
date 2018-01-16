module Ext-Typed.DTyped.Raw where

data Ctx : Set
data Sub : Set
data Ty  : Set
data Tm  : Set

data Ctx where
  ⋄   : Ctx
  _,_ : Ctx → Ty → Ctx

data Sub where
  _∘_   : Sub → Sub → Sub
  id    : Ctx → Sub
  <>    : Ctx → Sub
  p     : Ty → Sub
  <_,_> : Sub → Tm → Sub

data Ty where
  o     : Ty
  _[_]T : Ty → Sub → Ty

data Tm where
  _[_]t : Tm → Sub → Tm
  q     : Ty → Tm
  
dom     : Sub → Ctx
cod     : Sub → Ctx
ctx-of  : Ty → Ctx
type-of : Tm → Ty

dom (γ ∘ γ′)    = dom γ′
dom (id Γ)      = Γ
dom (<> Γ)      = Γ
dom (p A)       = ctx-of A , A
dom (< γ , _ >) = dom γ

cod (γ ∘ γ′)    = cod γ
cod (id Γ)      = Γ
cod (<> _)      = ⋄
cod (p A)       = ctx-of A
cod (< γ , α >) = cod γ , type-of α

ctx-of o          = ⋄
ctx-of (_ [ γ ]T) = dom γ

type-of (a [ γ ]t) = (type-of a) [ γ ]T
type-of (q A)      = A [ p A ]T

data _⊢    : Ctx → Set
data _⊢_   : Ctx → Ty → Set
data _⊢_∈_ : Ctx → Tm → Ty → Set
data _▹_⊢_ : Ctx → Ctx → Sub → Set

data _≡_⊢ : Ctx → Ctx → Set
data _⊢_≡_ : Ctx → Ty → Ty → Set

data _⊢ where

  c-emp : ⋄ ⊢
  
  c-ext : ∀ {Γ A}
          → Γ ⊢
          → Γ ⊢ A
          → (Γ , A) ⊢

data _⊢_ where

  ty-o : ∀ {Γ}
         → Γ ⊢
         → Γ ⊢ o

  ty-wf : ∀ {Γ Γ' A}
          → Γ ⊢ A
          → Γ ≡ Γ' ⊢
          → Γ' ⊢ A

  ty-sub : ∀ {Γ Δ A ρ}
           → Γ ⊢ A
           → Δ ▹ Γ ⊢ ρ
           → Δ ⊢ (A [ ρ ]T)

data _⊢_∈_ where

  tm-q : ∀ {Γ A}
         → (Γ , A) ⊢ q A ∈ A --(A [ ρ ]T)

data _▹_⊢_ where

  sub-⋄ : ∀ {Γ}
          → Γ ⊢
          → Γ ▹ ⋄ ⊢ <> Γ

  sub-id : ∀ {Γ A}
           → Γ ⊢ A
           → Γ ▹ Γ ⊢ id Γ

  sub-p : ∀ {Γ A}
          → Γ ⊢ A
          → (Γ , A) ▹ Γ ⊢ p A
  
data _≡_⊢ where

  c-eq-refl  : ∀ {Γ} → Γ ≡ Γ ⊢
  
  c-eq-sym   : ∀ {Γ Γ'}
               → Γ  ≡ Γ' ⊢
               → Γ' ≡ Γ  ⊢
               
  c-eq-trans : ∀ {Γ Γ' Γ''}
               → Γ  ≡ Γ'  ⊢
               → Γ' ≡ Γ'' ⊢
               → Γ  ≡ Γ'' ⊢

  c-eq-cong : ∀ {Γ Γ' A A'}
              → Γ ≡ Γ' ⊢
              → Γ ⊢ A ≡ A
              → (Γ , A) ≡ (Γ' , A') ⊢

data _⊢_≡_ where

  ty-eq-conv : ∀ {Γ Γ' A A'}
               → Γ ≡ Γ' ⊢
               → Γ' ⊢ A ≡ A'
               → Γ  ⊢ A ≡ A'

  ty-eq-idSub : ∀ {Γ A}
                → Γ ⊢
                → Γ ⊢ A
                → Γ ⊢ A [ id Γ ]T ≡ A

  ty-eq-compSub : ∀ {Γ Δ Θ A ρ₁ ρ₂}
                  → Θ ⊢ A
                  → Θ ▹ Δ ⊢ ρ₁
                  → Δ ▹ Γ ⊢ ρ₂
                  → Γ ⊢ (A [ ρ₁ ]T) [ ρ₂ ]T ≡ (A [ ρ₁ ∘ ρ₂ ]T)
                                

