-------------------------------------------------------------------------
-- Simply typed category with families based on raw untyped terms with
-- appropriate explicit typing rules for substitutions and terms
-- This contrasts the 'intrinsic' way of implementing types
-------------------------------------------------------------------------
module Ext-Typed.STyped.ScwfExt where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product using (Σ)
open import Data.Vec hiding ([_])
open import Ext-Typed.STyped.CtxType
open import Ext-Typed.STyped.ExtScwf
-------------------------------------------------------------------------
-- Raw terms substitutions

data RTm : Nat → Set
data RSub : Nat → Nat → Set

data RTm where
  q    : ∀ {n} → RTm (suc n)
  _[_] : ∀ {m n} (t : RTm n) (ρ : RSub m n) → RTm m
  app  : ∀ {n} (t u : RTm n) → RTm n
  lam  : ∀ {n} (t : RTm (suc n)) → RTm n

data RSub where
  <>    : ∀ {m} → RSub m zero
  id    : ∀ {n} → RSub n n
  p     : ∀ {n} → RSub (suc n) n
  <_,_> : ∀ {m n} → RSub m n → RTm m → RSub m (suc n)
  _∘_   : ∀ {m n k} → RSub n k → RSub m n → RSub m k
  
infix 4 _⊢_∈_
infix 4 _▹_⊢_

-- Typing rules for terms and substitutions

data _⊢_∈_ : ∀ {n} → Ctx n → RTm n → Ty → Set

data _▹_⊢_ : ∀ {m n} → Ctx m → Ctx n → RSub n m → Set

data _⊢_∈_ where

  q∈   : ∀ {n α} {Γ : Ctx n} → Γ ∙ α ⊢ q ∈ α

  sub∈ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {α t ρ}
         → Γ ⊢ t ∈ α
         → Γ ▹ Δ ⊢ ρ
         → Δ ⊢ t [ ρ ] ∈ α

  app∈ : ∀ {n} {Γ : Ctx n} {α β t u}
         → Γ ⊢ t ∈ (α ⇒ β)
         → Γ ⊢ u ∈ α
         → Γ ⊢ app t u ∈ β

  lam∈ : ∀ {n} {Γ : Ctx n} {α β t}
         → Γ ∙ α ⊢ t ∈ β
         → Γ ⊢ lam t ∈ (α ⇒ β)

data _▹_⊢_ where

  ⊢<> : ∀ {m} {Δ : Ctx m} → ε ▹ Δ ⊢ <>

  ⊢id : ∀ {n} {Γ : Ctx n} → Γ ▹ Γ ⊢ id
  
  ⊢p  : ∀ {n α} {Γ : Ctx n} → Γ ▹ Γ ∙ α ⊢ p

  ⊢∘  : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
          {ρ : RSub n k} {σ : RSub m n}
        → Θ ▹ Γ ⊢ ρ
        → Γ ▹ Δ ⊢ σ
        → Θ ▹ Δ ⊢ ρ ∘ σ
  
  ⊢<,> : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
           {t : RTm m} {ρ : RSub m n} {α}
         → Δ ⊢ t ∈ α
         → Γ ▹ Δ ⊢ ρ
         → Γ ∙ α ▹ Δ ⊢ < ρ , t >

-- example pairing of raw term with typing rule

sub : ∀ {m n α} {Δ : Ctx m} {Γ : Ctx n}
      → Σ (RTm n) (Γ ⊢_∈ α)
      → Σ (RSub m n) (Γ ▹ Δ ⊢_)
      → Σ (RTm m) (Δ ⊢_∈ α)             
sub (t Σ., t∈) (ρ Σ., ⊢ρ) = t [ ρ ] Σ., sub∈ t∈ ⊢ρ

infix 6 _≈_
infix 6 _≋_

-- Equality on raw terms and substitutions as equivalence relations with
-- cwf axioms

data _≈_ : ∀ {n} (t₁ t₂ : RTm n) → Set
data _≋_ : ∀ {m n} (ρ₁ ρ₂ : RSub m n) → Set

data _≈_ where

  clos  : ∀ {m n κ} (t : RTm n) (ts : RSub m n) (us : RSub κ m)
          → t [ ts ∘  us ] ≈ t [ ts ] [ us ]
             
  terId : ∀ {n} (t : RTm n)
          → t [ id ] ≈ t
          
  qCons : ∀ {m n} (t : RTm n) (ts : RSub n m)
          → q [ < ts , t > ] ≈ t

  appCm : ∀ {n m} (t u : RTm n) (ρ : RSub m n)
          → app (t [ ρ ]) (u [ ρ ]) ≈ app t u [ ρ ]
  
  lamCm : ∀ {n m} (t : RTm (suc n)) (ρ : RSub m n)
          → lam t [ ρ ] ≈ lam (t [ < ρ ∘ p , q > ])
          
  cong-sub : ∀ {m n} {t u : RTm n} {ts us : RSub m n}
             → t ≈ u
             → ts ≋ us
             → t [ ts ] ≈ u [ us ]

  cong-app : ∀ {n} {t u t′ u′ : RTm n}
             → t ≈ t′
             → u ≈ u′
             → app t u ≈ app t′ u′

  cong-lam : ∀ {n} {t u : RTm (suc n)}
             → t ≈ u
             → lam t ≈ lam u
        
  sym≈ : ∀ {n} {u u′ : RTm n}
         → u ≈ u′
         → u′ ≈ u
            
  trans≈ : ∀ {m} {t u v : RTm m}
           → t ≈ u
           → u ≈ v
           → t ≈ v             

data _≋_ where

  id₀ : id {0} ≋ <>
  
  ∘<> : ∀ {m n} (ts : RSub m n) → <> ∘ ts ≋ <>
          
  varp : ∀ {n} →  id {suc n} ≋ < p , q >
          
  idL : ∀ {m n} (ts : RSub m n) → id ∘ ts ≋ ts
  
  idR : ∀ {m n} (ts : RSub m n) → ts ∘ id ≋ ts
  
  assoc : ∀ {m n κ ι} (ts : RSub n κ) (us : RSub m n) (vs : RSub ι m)
          → (ts ∘ us) ∘ vs ≋ ts ∘ (us ∘ vs)
          
  pCons : ∀ {n κ} (t : RTm n) (ts : RSub n κ)
          → p ∘ < ts , t > ≋ ts
  
  maps : ∀ {m n} (t : RTm n) (ts : RSub n m) (us : RSub m n)
         → < ts , t > ∘ us ≋ < ts ∘ us , t [ us ] >
             
  cong-<,> : ∀ {m n} {t u : RTm m} {ts us : RSub m n}
             → t ≈ u
             → ts ≋ us
             → < ts , t > ≋ < us , u >
             
  cong-∘ : ∀ {m n k} {ts vs : RSub n k} {us zs : RSub m n}
           → ts ≋ vs
           → us ≋ zs
           → ts ∘ us ≋ vs ∘ zs
             
  sym≋ : ∀ {m n} {h t : RSub m n}
         → h ≋ t
         → t ≋ h
             
  trans≋ : ∀ {m n} {h t v : RSub m n}
           → h ≋ t
           → t ≋ v
           → h ≋ v
             
refl≈ : ∀ {n} {t : RTm n} → t ≈ t
refl≈ {t = t} = trans≈ (sym≈ (terId t)) (terId t)

refl≋ : ∀ {m n} {ρ : RSub m n} → ρ ≋ ρ
refl≋ {ρ = ρ} = trans≋ (sym≋ (idL ρ)) (idL ρ)

{-
ScwfInst : Scwf
ScwfInst = record
             { Tm    = RTm
             ; Sub   = RSub
             ; _≈_    = _≈_
             ; _≋_    = _≋_
             ; Ty     = Ty
             ; Ctx    = Ctx
             ; ε      = ε
             ; _∙_    = _∙_
             ; _⊢_∈_  = _⊢_∈_
             ; _▹_⊢_  = λ Γ Δ ρ → Δ ▹ Γ ⊢ ρ
             ; id-ty  = id Σ., ⊢id
             ; _∘_    = λ { (ρ Σ., ⊢ρ) (σ Σ., ⊢σ) → (ρ ∘ σ) Σ., (⊢∘ ⊢ρ ⊢σ) }
             ; q-ty   = q Σ., q∈
             ; p-ty   = p Σ., ⊢p
             ; <>-ty  = <> Σ., ⊢<>
             ; <,>-ty = λ { (ρ Σ., ⊢ρ) (t Σ., t∈) → < ρ , t > Σ., ⊢<,> t∈ ⊢ρ }
             ; sub-ty = λ { (t Σ., t∈) (ρ Σ., ⊢ρ) → (t [ ρ ]) Σ., sub∈ t∈ ⊢ρ }
             }

LamScwfInst : Lambda-Scwf
LamScwfInst = record
                { scwf   = ScwfInst
                ; _`→_   = _⇒_
                ; lam-ty = λ { (t Σ., t∈) → lam t Σ., lam∈ t∈ }
                ; app-ty = λ { (t Σ., t∈) (u Σ., u∈) → app t u Σ., app∈ t∈ u∈ } }
-}
