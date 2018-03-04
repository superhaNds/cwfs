-------------------------------------------------------------------------------
-- Properties and lemmata needed for various proofs
-------------------------------------------------------------------------------
module SimpTyped.ImpSub.Properties where

open import Data.Nat renaming (ℕ to Nat)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import SimpTyped.Type
open import SimpTyped.Context
open import Function as F using (_$_ ; flip)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import SimpTyped.ImpSub.Syntax
open import SimpTyped.Scwf
open P.≡-Reasoning

abstract

  wk-refl : ∀ {Γ α} (t : Tm Γ α) → weaken ⊆-refl t ≡ t
  wk-refl (var ∈Γ) = var-eq (sub-in-refl ∈Γ)
  wk-refl (ƛ t)    = cong ƛ (wk-refl t)
  wk-refl (t · u)  = cong₂ _·_ (wk-refl t) (wk-refl u)

  wk-sub-refl : ∀ {Δ} Γ (ρ : Sub Δ Γ) → wk-sub Γ (⊆-refl) ρ ≡ ρ
  wk-sub-refl ε tt            = refl
  wk-sub-refl (Γ ∙ x) (ρ , t) = cong₂ _,_ (wk-sub-refl Γ ρ) (wk-refl t) 

  wk-tr : ∀ {Γ Δ Θ α} (φ : Γ ⊆ Δ) (ψ : Δ ⊆ Θ) (t : Tm Γ α)
          → weaken ψ (weaken φ t) ≡ weaken (⊆-trans φ ψ) t
  wk-tr φ ψ (var ∈Γ) = cong var (sub-in₂ φ ψ ∈Γ)
  wk-tr φ ψ (t · u)  = cong₂ _·_ (wk-tr φ ψ t) (wk-tr φ ψ u)
  wk-tr φ ψ (ƛ t)    = cong ƛ (wk-tr (pop! φ) (pop! ψ) t)

  tk-weaken : ∀ {Γ Δ Θ α} (φ : α ∈ Γ) (i : Δ ⊆ Θ) (ρ : Sub Δ Γ)
              → weaken i (tkVar φ ρ) ≡ tkVar φ (wk-sub Γ i ρ)
  tk-weaken here i ρ = refl
  tk-weaken (there φ) i (ρ , t) = tk-weaken φ i ρ

  ▹-wk-simp : ∀ {Γ Δ E Θ} (v₁ : Γ ⊆ Δ) (v₂ : E ⊆ Θ) (ρ : Sub E Δ)
              → wk-sub Γ v₂ (simp v₁ ρ) ≡ simp v₁ (wk-sub Δ v₂ ρ)
  ▹-wk-simp base      v₂ ρ       = refl
  ▹-wk-simp (step v₁) v₂ (ρ , _) = ▹-wk-simp v₁ v₂ ρ
  ▹-wk-simp (pop! v₁) v₂ (ρ , α) = cong (_, weaken v₂ α) (▹-wk-simp v₁ v₂ ρ)

  simp-refl : ∀ (Γ {Δ} : Ctx) (ρ : Sub Δ Γ) → simp ⊆-refl ρ ≡ ρ
  simp-refl ε tt = refl
  simp-refl (Γ ∙ x) (ρ , t) = cong (_, t) (simp-refl Γ ρ)

  ▹-wk-2 : ∀ {Δ E Θ} Γ
             (φ : Δ ⊆ E)
             (ψ : E ⊆ Θ)
             (ρ : Sub Δ Γ)
           → wk-sub Γ ψ (wk-sub Γ φ ρ) ≡ wk-sub Γ (⊆-trans φ ψ) ρ
  ▹-wk-2 ε       φ ψ ρ       = refl
  ▹-wk-2 (Γ ∙ α) φ ψ (ρ , t) = cong₂ _,_ (▹-wk-2 Γ φ ψ ρ) (wk-tr φ ψ t)

  []-wk : ∀ {Γ Δ N α} (φ : Δ ⊆ N) (t : Tm Γ α) (ρ : Sub Δ Γ)
          → weaken φ (t [ ρ ]) ≡ t [ wk-sub Γ φ ρ ]
  []-wk φ (var ∈Γ) ρ = tk-weaken ∈Γ φ ρ
  []-wk φ (t · u) ρ = cong₂ _·_ ([]-wk φ t ρ) ([]-wk φ u ρ)
  []-wk {Γ} {Δ} φ (ƛ t) ρ =
    cong ƛ (trans ([]-wk (pop! φ) t
                   (wk-sub Γ (step ⊆-refl) ρ , var here))
           (cong (t [_] F.∘ (_, var here)) 
                 (trans (▹-wk-2 Γ (step ⊆-refl) (pop! φ) ρ)
                        (trans (cong (λ x → wk-sub Γ x ρ) (⊆-step-refl φ))
                        (sym $ ▹-wk-2 Γ φ (step ⊆-refl) ρ)))))

  wk-∘ : ∀ (Γ {Δ} {E} {Θ} : Ctx) (φ : E ⊆ Θ)
           (ρ : Sub Δ Γ) (σ : Sub E Δ)
         → ρ ∘ (wk-sub Δ φ σ) ≡ wk-sub Γ φ (ρ ∘ σ)
  wk-∘ ε       φ ρ       σ = refl
  wk-∘ (Γ ∙ x) φ (ρ , t) σ = cong-, (sym ([]-wk φ t σ)) (wk-∘ Γ φ ρ σ)

  tk-∘ : ∀ {Γ Δ Θ α} (φ : α ∈ Γ)
           (ρ : Sub Δ Γ) (σ : Sub Θ Δ)
         → (tkVar φ ρ) [ σ ] ≡ tkVar φ (ρ ∘ σ)
  tk-∘ here ρ σ = refl
  tk-∘ (there φ) (ρ , _) σ = tk-∘ φ ρ σ

  tk-in : ∀ {Γ Δ Θ α} (φ : Γ ⊆ Δ)
            (v : α ∈ Γ) (ρ : Sub Θ Δ)
          → tkVar (sub-in φ v) ρ ≡ tkVar v (simp φ ρ)
  tk-in (step φ) here      (ρ , t) = tk-in φ here ρ
  tk-in (step φ) (there v) (ρ , t) = tk-in φ (there v) ρ
  tk-in (pop! φ) here      _       = refl
  tk-in (pop! φ) (there v) (ρ , t) = tk-in φ v ρ

  wk-[] : ∀ {Γ Δ Θ α} (v : Γ ⊆ Δ) (t : Tm Γ α) (ρ : Sub Θ Δ)
          → (weaken v t) [ ρ ] ≡ t [ simp v ρ ]
  wk-[] v (var ∈Γ) ρ = tk-in v ∈Γ ρ
  wk-[] v (t · u)  ρ = cong₂ _·_ (wk-[] v t ρ) (wk-[] v u ρ)
  wk-[] {Γ} {Δ} v (ƛ t) ρ = cong ƛ
    (trans (wk-[] (pop! v) t (wk-sub Δ ⊆-∙ ρ , var here))
           (cong (λ ρ → t [ ρ , var here ]) (sym (▹-wk-simp v ⊆-∙ ρ))))

  ∘-step : ∀ Γ {Δ} {Θ} {α} (ρ : Sub Δ Γ)
             (σ : Sub Θ Δ) (t : Tm Θ α)
           → (wk-sub Γ ⊆-∙ ρ) ∘ (σ , t) ≡ ρ ∘ σ
  ∘-step ε ρ σ t = refl
  ∘-step (Γ ∙ x) (ρ , u) σ t =
    cong₂ _,_ (∘-step Γ ρ σ t)
              (trans (wk-[] (step ⊆-refl) u (σ , t))
                     (cong (u [_]) (simp-refl _ σ)))
               
  ▹-wk-refl : ∀ Γ {Δ} (ρ : Sub Δ Γ) → wk-sub Γ ⊆-refl ρ ≡ ρ
  ▹-wk-refl ε tt = refl
  ▹-wk-refl (Γ ∙ _) (ρ , t) = cong₂ _,_ (▹-wk-refl Γ ρ) (wk-refl t)

  tkVar-wk-id : ∀ {Γ Δ α} (v : α ∈ Γ) (φ : Γ ⊆ Δ)
                → tkVar v (wk-sub Γ φ id) ≡ var (sub-in φ v)
  tkVar-wk-id {ε} () φ
  tkVar-wk-id {Γ ∙ x} here φ = refl
  tkVar-wk-id {Γ ∙ x} (there v) φ =
    trans (cong (tkVar v) (▹-wk-2 Γ (step ⊆-refl) φ id))
          (trans (tkVar-wk-id v (⊆-trans (step ⊆-refl) φ))
                 (cong var (sub-in-step φ v)))

  tkVar-p : ∀ {Γ α} (v : α ∈ Γ) → tkVar v (p {α = α}) ≡ var (there v)
  tkVar-p {Γ} v = trans (tkVar-wk-id v (step ⊆-refl))
                        (cong (var F.∘ there) (sub-in-refl v))

  tkVar-id : ∀ {Γ α} (v : α ∈ Γ) → tkVar v id ≡ var v
  tkVar-id here = refl
  tkVar-id {Γ = Γ ∙ x} (there v) =
    trans (tkVar-wk-id v ⊆-∙)
          (cong (var F.∘ there) (sub-in-refl v))

  lim : ∀ {Γ Δ α} (ρ : Δ ▸ Γ) (v : α ∈ Γ) → var (tk∈ v ρ) ≡ tkVar v (▸-to-sub var ρ)
  lim {Γ ∙ x} (ρ , t) here      = refl
  lim {Γ ∙ x} (ρ , t) (there v) = lim ρ v

  wk-∈ : ∀ {Γ Δ Θ} {α : Ty} (φ : Γ ⊆ Δ) (ψ : Δ ⊆ Θ) (v : α ∈ Γ)
         → sub-in ψ (sub-in φ v) ≡ sub-in (⊆-trans φ ψ) v
  wk-∈ φ ψ v = sub-in₂ φ ψ v
  
  ▸-wk-2 : ∀ {Δ E Θ} Γ (φ : Δ ⊆ E) (ψ : E ⊆ Θ) (ρ : Δ ▸ Γ)
           → ▸-weaken Γ ψ (▸-weaken Γ φ ρ) ≡ ▸-weaken Γ (⊆-trans φ ψ) ρ
  ▸-wk-2 ε φ ψ tt = refl
  ▸-wk-2 (Γ ∙ x) φ ψ (ρ , t) = cong₂ _,_ (▸-wk-2 Γ φ ψ ρ) (wk-∈ φ ψ t)           

  tk∈-wk-id : ∀ {Γ Δ α} (v : α ∈ Γ) (φ : Γ ⊆ Δ)
              → tk∈ v (▸-weaken Γ φ idV) ≡ sub-in φ v
  tk∈-wk-id here φ = refl
  tk∈-wk-id (there v) φ =
    trans (cong (tk∈ v) (▸-wk-2 _ (step ⊆-refl) φ idV))
          (trans (tk∈-wk-id v (⊆-trans (step ⊆-refl) φ)) (sub-in-step φ v)) 

  tk∈-id : ∀ {Γ α} (v : α ∈ Γ) → tk∈ v idV ≡ v
  tk∈-id here      = refl
  tk∈-id (there v) = trans (tk∈-wk-id v (step ⊆-refl)) (cong there (sub-in-refl v))

  pVar : ∀ {Γ α} → (Γ ∙ α) ▸ Γ
  pVar {Γ} = ▸-weaken Γ ⊆-∙ idV

  tk∈-wk-there : ∀ {Γ α} (v : α ∈ Γ) → tk∈ v (pVar {α = α}) ≡ there v
  tk∈-wk-there {Γ ∙ _} here = refl
  tk∈-wk-there {Γ ∙ x} (there v) =
    trans (trans (cong (tk∈ v)
     (▸-wk-2 Γ (step ⊆-refl) (step (pop! ⊆-refl)) idV))
     (trans (tk∈-wk-id {Γ} v (step (step (⊆-trans ⊆-refl ⊆-refl))))
      (cong (there F.∘ there F.∘ flip sub-in v) ⊆-trans-refl))) 
      (cong (there F.∘ there) (sub-in-refl v))

  tkVar-pV : ∀ {Γ α} (v : α ∈ Γ) → tkVar v (▸-to-sub var (pVar {Γ} {α})) ≡ var (there v)
  tkVar-pV here = refl
  tkVar-pV {Γ ∙ x} (there v) =
    trans (sym (lim pVar (there v)))
          (cong var (trans (tk∈-wk-there (there v)) refl))

  tkVar-idV : ∀ {Γ α} (v : α ∈ Γ) → tkVar v (▸-to-sub var (idV {Γ})) ≡ var v
  tkVar-idV here = refl
  tkVar-idV {Γ ∙ x} (there v) =
    trans (sym (lim idV (there v)))
          (cong var (trans (tk∈-wk-id v (step ⊆-refl))
                           (cong there (sub-in-refl v))))

  tkV-p-map : ∀ {Γ α} (v : α ∈ Γ) → tkVar v (▸-to-sub var (pV {α = α})) ≡ var (there v)
  tkV-p-map here = refl
  tkV-p-map {Γ ∙ x} (there v)
    = trans (sym (lim pV (there v))) (cong var (tk∈-pV-th (there v)))

  for-all-tk : ∀ {Γ Δ} (γ γ' : Sub Δ Γ)
                 (hyp : ∀ {α} (v : α ∈ Γ) → tkVar v γ ≡ tkVar v γ')
              → γ ≡ γ'
  for-all-tk {ε} tt tt hyp = refl
  for-all-tk {Γ ∙ _} (γ , t) (γ' , t') hyp
    = cong₂ _,_ (for-all-tk γ γ' (λ v → hyp (there v))) (hyp here)
 
  p-tk-same : ∀ {Γ α} (v : α ∈ Γ)
              → tkVar v (▸-to-sub var (pV {α = α})) ≡ tkVar v p
  p-tk-same v = sym (trans (tkVar-p v) (sym (tkV-p-map v)))
  
  postulate  pIsVarP : ∀ {Γ α} → ▸-to-sub var (pV {Γ} {α}) ≡ p {Γ} {α}
 -- pIsVarP {Γ} {α} = for-all-tk (▸-to-sub var (pV {Γ})) p {!p-tk-same!}
  
  subId : ∀ {Γ α} (t : Tm Γ α) → t [ id ] ≡ t
  subId (var ∈Γ) = tkVar-id ∈Γ
  subId (t · u)  = cong₂ _·_ (subId t) (subId u)
  subId (ƛ t)    = cong ƛ (subId t)

  idR : ∀ {Γ Δ} (ρ : Sub Γ Δ) → ρ ∘ id ≡ ρ
  idR {Δ = ε}     tt      = refl
  idR {Δ = Δ ∙ x} (ρ , t) =
    trans (cong (_, t [ id ]) (idR ρ))
          (cong (ρ ,_) (subId t))

  sub-p : ∀ {Γ α β} (t : Tm Γ α) → t [ p {α = β} ] ≡ weaken ⊆-∙ t
  sub-p {Γ} t = begin
    t [ p ]                 ≡⟨⟩
    t [ wk-sub Γ ⊆-∙ id ]   ≡⟨ sym ([]-wk ⊆-∙ t id) ⟩
    weaken ⊆-∙ (t [ id ] )  ≡⟨ cong (weaken ⊆-∙) (subId t) ⟩ 
    weaken ⊆-∙ t            ∎
    where open P.≡-Reasoning

  wk-[p] : ∀ {Γ α} (t : Tm Γ α) → weaken (step {σ = α} ⊆-refl) t ≡ t [ p ]
  wk-[p] t = sym $ sub-p t

  wk-sub-∘-p : ∀ {Γ Δ α} (ρ : Sub Δ Γ) → ρ ∘ p {α = α} ≡ wk-sub Γ ⊆-∙ ρ
  wk-sub-∘-p {ε} tt = refl
  wk-sub-∘-p {Γ ∙ α} (ρ , t) = begin
    ρ ∘ p , t [ p ]                 ≡⟨ cong (ρ ∘ p ,_) (sub-p t) ⟩
    ρ ∘ p , weaken ⊆-∙ t            ≡⟨ cong (_, weaken ⊆-∙ t )(wk-sub-∘-p ρ) ⟩
    wk-sub Γ ⊆-∙ ρ , weaken ⊆-∙ t   ∎
    where open P.≡-Reasoning

  id₀ : id {ε} ≡ tt
  id₀ = refl
