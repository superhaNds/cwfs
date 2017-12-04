module Unityped.Wellscoped.Typed.ScwfExt where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product using (Σ)
open import Data.Vec hiding ([_])
open import Unityped.Wellscoped.Typed.CtxType

data RTm : Nat → Set
data Subst : Nat → Nat → Set

data RTm where
  q    : ∀ {n} → RTm (suc n)
  _[_] : ∀ {m n} (t : RTm n) (ρ : Subst m n) → RTm m
  app  : ∀ {n} (t u : RTm n) → RTm n
  lam  : ∀ {n} (t : RTm (suc n)) → RTm n

data Subst where
  <>    : ∀ {m} → Subst m zero
  id    : ∀ {n} → Subst n n
  p     : ∀ {n} → Subst (suc n) n
  <_,_> : ∀ {m n} → Subst m n → RTm m → Subst m (suc n)
  _∘_   : ∀ {m n k} → Subst n k → Subst m n → Subst m k
  
infix 4 _⊢_∈_
infix 4 _▹_⊢_

data _⊢_∈_ : ∀ {n} → Ctx n → RTm n → Ty → Set

data _▹_⊢_ : ∀ {m n} → Ctx m → Ctx n → Subst n m → Set

data _⊢_∈_ where

  ⊢q   : ∀ {n α} {Γ : Ctx n} →

         ------------------
           Γ , α ⊢ q ∈ α

  []∈ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {α t ρ} →
  
        Γ ⊢ t ∈ α → Γ ▹ Δ ⊢ ρ →
        ------------------------
            Δ ⊢ t [ ρ ] ∈ α

  app∈ : ∀ {n} {Γ : Ctx n} {α β t u} →

         Γ ⊢ t ∈ (α ⇨ β) → Γ ⊢ u ∈ α →
         ---------------------------
            Γ ⊢ app t u ∈ β

  lam∈ : ∀ {n} {Γ : Ctx n} {α β t} →

           Γ , α ⊢ t ∈ β →
         --------------------
          Γ ⊢ lam t ∈ (α ⇨ β)

data _▹_⊢_ where

  ⊢<> : ∀ {m} {Δ : Ctx m} →

        ----------------
           ε ▹ Δ ⊢ <>

  ⊢id : ∀ {n} {Γ : Ctx n} →

        ---------------
          Γ ▹ Γ ⊢ id
  
  ⊢p  : ∀ {n α} {Γ : Ctx n} →

        -------------------
           Γ ▹ Γ , α ⊢ p

  ⊢∘  : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
          {ρ : Subst n k} {σ : Subst m n} →
          
        Θ ▹ Γ ⊢ ρ → Γ ▹ Δ ⊢ σ → 
        -------------------------
             Θ ▹ Δ ⊢ ρ ∘ σ
  
  ⊢<,> : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
           {t : RTm m} {ρ : Subst m n} {α} →
         
         Δ ⊢ t ∈ α → Γ ▹ Δ ⊢ ρ →
         -------------------------
           Γ , α ▹ Δ ⊢ < ρ , t >

sub : ∀ {m n α} {Δ : Ctx m} {Γ : Ctx n} → Σ (RTm n) (Γ ⊢_∈ α) →
      Σ (Subst m n) (Γ ▹ Δ ⊢_) → Σ (RTm m) (Δ ⊢_∈ α)             
sub (t Σ., t∈) (ρ Σ., ⊢ρ) = t [ ρ ] Σ., []∈ t∈ ⊢ρ


infix 6 _~_
infix 6 _~~_

data _~_ : ∀ {n} (t₁ t₂ : RTm n) → Set
data _~~_ : ∀ {m n} (ρ₁ ρ₂ : Subst m n) → Set

data _~_ where

  clos  : ∀ {m n κ} (t : RTm n) (ts : Subst m n) (us : Subst κ m) →
          t [ ts ∘  us ] ~ t [ ts ] [ us ]
             
  terId : ∀ {n} (t : RTm n) →
          t [ id ] ~ t
          
  qCons : ∀ {m n} (t : RTm n) (ts : Subst n m) →
          q [ < ts , t > ] ~ t

  appCm : ∀ {n m} (t u : RTm n) (ρ : Subst m n) →
          app (t [ ρ ]) (u [ ρ ]) ~ app t u [ ρ ]
  
  lamCm : ∀ {n m} (t : RTm (suc n)) (ρ : Subst m n) →
          lam t [ ρ ] ~ lam (t [ < ρ ∘ p , q > ])
          
  cong-[] : ∀ {m n} {t u : RTm n} {ts us : Subst m n} →
            t ~ u → ts ~~ us → t [ ts ] ~ u [ us ]

  cong-app : ∀ {n} {t u t′ u′ : RTm n} →
             t ~ t′ → u ~ u′ → app t u ~ app t′ u′

  cong-lam : ∀ {n} {t u : RTm (suc n)} →
             t ~ u → lam t ~ lam u
        
  sym~ : ∀ {n} {u u′ : RTm n} →
         u ~ u′ → u′ ~ u
            
  trans~ : ∀ {m} {t u v : RTm m} →
           t ~ u → u ~ v → t ~ v             

data _~~_ where

  id₀ : id {0} ~~ <>
  
  ∘<> : ∀ {m n} (ts : Subst m n) →
         <> ∘ ts ~~ <>
          
  varp : ∀ {n} →
         id {suc n} ~~ < p , q >
          
  idL : ∀ {m n} (ts : Subst m n) →
        id ∘ ts ~~ ts
  
  idR : ∀ {m n} (ts : Subst m n) →
        ts ∘ id ~~ ts
  
  assoc : ∀ {m n κ ι} (ts : Subst n κ) (us : Subst m n) (vs : Subst ι m) →
          (ts ∘ us) ∘ vs ~~ ts ∘ (us ∘ vs)
          
  pCons : ∀ {n κ} → (t : RTm n) → (ts : Subst n κ) →
          p ∘ < ts , t > ~~ ts
  
  maps : ∀ {m n} (t : RTm n) (ts : Subst n m) (us : Subst m n) →
         < ts , t > ∘ us ~~ < ts ∘ us , t [ us ] >
             
  cong-<,> : ∀ {m n} {t u : RTm m} {ts us : Subst m n} →
             t ~ u → ts ~~ us → < ts , t > ~~ < us , u >
             
  cong-∘ : ∀ {m n k} {ts vs : Subst n k} {us zs : Subst m n} →
           ts ~~ vs → us ~~ zs → ts ∘ us ~~ vs ∘ zs
             
  sym~~ : ∀ {m n} {h t : Subst m n} →
          h ~~ t → t ~~ h
             
  trans~~ : ∀ {m n} {h t v : Subst m n} →
            h ~~ t → t ~~ v → h ~~ v
             
refl~ : ∀ {n} {t : RTm n} → t ~ t
refl~ {t = t} = trans~ (sym~ (terId t)) (terId t)

refl~~ : ∀ {m n} {ρ : Subst m n} → ρ ~~ ρ
refl~~ {ρ = ρ} = trans~~ (sym~~ (idL ρ)) (idL ρ)
