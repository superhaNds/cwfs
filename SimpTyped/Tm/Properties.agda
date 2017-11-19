module SimpTyped.Tm.Properties where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import SimpTyped.Type
open import SimpTyped.Context
open import Function using (_$_ ; _∘_ ; flip)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import SimpTyped.Tm.Syntax
open import SimpTyped.Scwf
open P.≡-Reasoning

abstract

  wk-refl : ∀ {Γ α} (t : Term Γ α) → weaken ⊆-refl t ≡ t
  wk-refl (var ∈Γ) = var-eq (sub-in-refl ∈Γ)
  wk-refl (ƛ t)    = cong ƛ (wk-refl t)
  wk-refl (t · u)  = cong₂ _·_ (wk-refl t) (wk-refl u)

  wk-sub-refl : ∀ {Δ} Γ (ρ : Δ ▹ Γ) → ▹-weaken Γ (⊆-refl) ρ ≡ ρ
  wk-sub-refl ε tt            = refl
  wk-sub-refl (Γ ∙ x) (t , ρ) = cong₂ _,_ (wk-refl t) (wk-sub-refl Γ ρ)

  wk-tr : ∀ {Γ Δ Θ α} (φ : Γ ⊆ Δ) (ψ : Δ ⊆ Θ) (t : Term Γ α) →
               weaken ψ (weaken φ t) ≡ weaken (⊆-trans φ ψ) t
  wk-tr φ ψ (var ∈Γ) = cong var (sub-in₂ φ ψ ∈Γ)
  wk-tr φ ψ (t · u)  = cong₂ _·_ (wk-tr φ ψ t) (wk-tr φ ψ u)
  wk-tr φ ψ (ƛ t)    = cong ƛ (wk-tr (pop! φ) (pop! ψ) t)

  tk-weaken : ∀ {Γ Δ Θ α} (φ : α ∈ Γ) (i : Δ ⊆ Θ) (ρ : Δ ▹ Γ) →
              weaken i (tkVar φ ρ) ≡ tkVar φ (▹-weaken Γ i ρ)
  tk-weaken here i ρ = refl
  tk-weaken (there φ) i (t , ρ) = tk-weaken φ i ρ

  ▹-wk-simp : ∀ {Γ Δ E Θ} (v₁ : Γ ⊆ Δ) (v₂ : E ⊆ Θ) (ρ : E ▹ Δ) →
              ▹-weaken Γ v₂ (simp v₁ ρ) ≡ simp v₁ (▹-weaken Δ v₂ ρ)
  ▹-wk-simp base      v₂ ρ       = refl
  ▹-wk-simp (step v₁) v₂ (_ , ρ) = ▹-wk-simp v₁ v₂ ρ
  ▹-wk-simp (pop! v₁) v₂ (α , ρ) = cong (_,_ (weaken v₂ α)) (▹-wk-simp v₁ v₂ ρ)            

  simp-refl : ∀ (Γ {Δ} : Ctx) (ρ : Δ ▹ Γ) → simp ⊆-refl ρ ≡ ρ
  simp-refl ε tt = refl
  simp-refl (Γ ∙ x) (t , ρ) = cong (t ,_) (simp-refl Γ ρ)

  ▹-wk-2 : ∀ {Δ E Θ} Γ (φ : Δ ⊆ E) (ψ : E ⊆ Θ) (ρ : Δ ▹ Γ) →
           ▹-weaken Γ ψ (▹-weaken Γ φ ρ) ≡ ▹-weaken Γ (⊆-trans φ ψ) ρ
  ▹-wk-2 ε       φ ψ ρ       = refl
  ▹-wk-2 (Γ ∙ α) φ ψ (t , ρ) = cong₂ _,_ (wk-tr φ ψ t) (▹-wk-2 Γ φ ψ ρ)    

  []-wk : ∀ {Γ Δ N α} (φ : Δ ⊆ N) (t : Term Γ α) (ρ : Δ ▹ Γ) →
          weaken φ (t [ ρ ]) ≡ t [ ▹-weaken Γ φ ρ ]
  []-wk φ (var ∈Γ) ρ = tk-weaken ∈Γ φ ρ
  []-wk φ (t · u) ρ = cong₂ _·_ ([]-wk φ t ρ) ([]-wk φ u ρ)
  []-wk {Γ} {Δ} φ (ƛ t) ρ =
    cong ƛ (trans ([]-wk (pop! φ) t
             (var here , ▹-weaken Γ (step ⊆-refl) ρ))
      (cong (λ ρ → t [ (var here , ρ) ])
            (trans (▹-wk-2 Γ (step ⊆-refl) (pop! φ) ρ)
      (trans (cong (λ x → ▹-weaken Γ x ρ) (⊆-step-refl φ))
             (sym (▹-wk-2 Γ φ (step ⊆-refl) ρ))))))

  wk-⋆ : ∀ (Γ {Δ} {E} {Θ} : Ctx) (φ : E ⊆ Θ) (ρ : Δ ▹ Γ) (σ : E ▹ Δ) →
         ρ ⋆ (▹-weaken Δ φ σ) ≡ ▹-weaken Γ φ (ρ ⋆ σ)
  wk-⋆ ε       φ ρ       σ = refl
  wk-⋆ (Γ ∙ x) φ (t , ρ) σ = cong-, (sym ([]-wk φ t σ)) (wk-⋆ Γ φ ρ σ)

  tk-⋆ : ∀ {Γ Δ Θ α} (φ : α ∈ Γ) (ρ : Δ ▹ Γ) (σ : Θ ▹ Δ) →
         (tkVar φ ρ) [ σ ] ≡ tkVar φ (ρ ⋆ σ)
  tk-⋆ here ρ σ = refl
  tk-⋆ (there φ) (t , ρ) σ = tk-⋆ φ ρ σ

  tk-in : ∀ {Γ Δ Θ α} (φ : Γ ⊆ Δ) (v : α ∈ Γ) (ρ : Θ ▹ Δ) →
          tkVar (sub-in φ v) ρ ≡ tkVar v (simp φ ρ)
  tk-in (step φ) here      (t , ρ) = tk-in φ here ρ
  tk-in (step φ) (there v) (t , ρ) = tk-in φ (there v) ρ
  tk-in (pop! φ) here      _       = refl
  tk-in (pop! φ) (there v) (t , ρ) = tk-in φ v ρ

  wk-[] : ∀ {Γ Δ Θ α} (v : Γ ⊆ Δ) (t : Term Γ α) (ρ : Θ ▹ Δ) →
          (weaken v t) [ ρ ] ≡ t [ simp v ρ ]
  wk-[] v (var ∈Γ) ρ = tk-in v ∈Γ ρ
  wk-[] v (t · u)  ρ = cong₂ _·_ (wk-[] v t ρ) (wk-[] v u ρ)
  wk-[] {Γ} {Δ} v (ƛ t) ρ = cong ƛ
    (trans (wk-[] (pop! v) t (var here , ▹-weaken Δ ⊆-∙ ρ))
           (cong (λ ρ → t [ (var here , ρ) ]) (sym (▹-wk-simp v ⊆-∙ ρ))))

  ⋆-step : ∀ Γ {Δ} {Θ} {α} → (ρ : Δ ▹ Γ) (σ : Θ ▹ Δ) (t : Term Θ α) →
          (▹-weaken Γ ⊆-∙ ρ) ⋆ (t , σ) ≡ ρ ⋆ σ
  ⋆-step ε ρ σ t = refl
  ⋆-step (Γ ∙ x) (u , ρ) σ t =
    cong₂ _,_ (trans (wk-[] (step ⊆-refl) u (t , σ))
                     (cong (u [_]) (simp-refl _ σ)))
              (⋆-step Γ ρ σ t) 

  ▹-wk-refl : ∀ Γ {Δ} (ρ : Δ ▹ Γ) → ▹-weaken Γ ⊆-refl ρ ≡ ρ
  ▹-wk-refl ε tt = refl
  ▹-wk-refl (Γ ∙ x) (t , ρ) = cong₂ _,_ (wk-refl t) (▹-wk-refl Γ ρ)

  tkVar-wk-id : ∀ {Γ Δ α} (v : α ∈ Γ) (φ : Γ ⊆ Δ) →
                tkVar v (▹-weaken Γ φ id) ≡ var (sub-in φ v)
  tkVar-wk-id {ε} () φ
  tkVar-wk-id {Γ ∙ x} here φ = refl
  tkVar-wk-id {Γ ∙ x} (there v) φ =
    trans (cong (tkVar v) (▹-wk-2 Γ (step ⊆-refl) φ id))
          (trans (tkVar-wk-id v (⊆-trans (step ⊆-refl) φ))
                 (cong var (sub-in-step φ v)))

  tkVar-id : ∀ {Γ α} (v : α ∈ Γ) → tkVar v id ≡ var v
  tkVar-id here = refl
  tkVar-id {Γ = Γ ∙ x} (there v) =
    trans (tkVar-wk-id v ⊆-∙)
          (cong (var ∘ there) (sub-in-refl v))

  t[id] : ∀ {Γ α} (t : Term Γ α) → t [ id ] ≡ t
  t[id] (var ∈Γ) = tkVar-id ∈Γ
  t[id] (t · u)  = cong₂ _·_ (t[id] t) (t[id] u)
  t[id] (ƛ t)    = cong ƛ (t[id] t)

  idR : ∀ {Γ Δ} (ρ : Γ ▹ Δ) → ρ ⋆ id ≡ ρ
  idR {Δ = ε}     tt      = refl
  idR {Δ = Δ ∙ x} (t , ρ) =
    trans (cong (t [ id ] ,_) (idR ρ))
          (cong (_, ρ) (t[id] t))

  sub-p : ∀ {Γ α β} (t : Term Γ α) → t [ p {α = β} ] ≡ weaken ⊆-∙ t
  sub-p {Γ} t = begin
    t [ p ]                 ≡⟨⟩
    t [ ▹-weaken Γ ⊆-∙ id ] ≡⟨ sym ([]-wk ⊆-∙ t id) ⟩
    weaken ⊆-∙ (t [ id ] )  ≡⟨ cong (weaken ⊆-∙) (t[id] t) ⟩ 
    weaken ⊆-∙ t            ∎
    where open P.≡-Reasoning

  wk-[p] : ∀ {Γ α} (t : Term Γ α) →
           weaken (step {σ = α} ⊆-refl) t ≡ t [ p ]
  wk-[p] t = sym $ sub-p t

  ▹-weaken-⋆-p : ∀ {Γ Δ α} (ρ : Δ ▹ Γ) → ρ ⋆ p {α = α} ≡ ▹-weaken Γ ⊆-∙ ρ
  ▹-weaken-⋆-p {ε} tt = refl
  ▹-weaken-⋆-p {Γ ∙ α} (t , ρ) = begin
    t [ p ] , ρ ⋆ p                 ≡⟨ cong (_, ρ ⋆ p) (sub-p t) ⟩
    weaken ⊆-∙ t , ρ ⋆ p            ≡⟨ cong (weaken ⊆-∙ t ,_) (▹-weaken-⋆-p ρ) ⟩
    weaken ⊆-∙ t , ▹-weaken Γ ⊆-∙ ρ ∎
    where open P.≡-Reasoning

  idε<> : id {ε} ≡ tt
  idε<> = refl
