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

wk-refl : ∀ {Γ α} (t : Term Γ α) → weaken ⊆-refl t ≡ t
wk-refl (var ∈Γ) = var-eq (sub-in-refl ∈Γ)

wk-sub-refl : ∀ {Δ} Γ (ρ : Δ ▹ Γ) → ▹-weaken Γ (⊆-refl) ρ ≡ ρ
wk-sub-refl ε tt            = refl
wk-sub-refl (Γ ∙ x) (t , ρ) = cong₂ _,_ (wk-refl t) (wk-sub-refl Γ ρ)

wk-tr : ∀ {Γ Δ Θ α} (φ : Γ ⊆ Δ) (ψ : Δ ⊆ Θ) (t : Term Γ α) →
             weaken ψ (weaken φ t) ≡ weaken (⊆-trans φ ψ) t
wk-tr φ ψ (var ∈Γ) = cong var (sub-in₂ φ ψ ∈Γ)

id=<pq> : ∀ {Γ α} → id {Γ ∙ α} ≡ (q , p)
id=<pq> {ε}     = refl
id=<pq> {Γ ∙ x} = refl

[] : ∀ {Γ} → Γ ▹ ε
[] = tt

⋆-<> : ∀ {Γ Δ} (ρ : Γ ▹ Δ) → [] {Γ} ⋆ ρ ≡ [] {Γ}
⋆-<> _ = refl

q[] : ∀ {Γ Δ α} (t : Term Γ α) (ρ : Γ ▹ Δ) → q [ t , ρ ] ≡ t
q[] t ρ = refl

tk-weaken : ∀ {Γ Δ Θ α} (φ : α ∈ Γ) (i : Δ ⊆ Θ) (ρ : Δ ▹ Γ) →
            weaken i (tkVar φ ρ) ≡ tkVar φ (▹-weaken Γ i ρ)
tk-weaken here i ρ = refl
tk-weaken (there φ) i (t , ρ) = tk-weaken φ i ρ            

simp-refl : ∀ (Γ {Δ} : Ctx) (ρ : Δ ▹ Γ) → simp ⊆-refl ρ ≡ ρ
simp-refl ε tt = refl
simp-refl (Γ ∙ x) (t , ρ) = cong (t ,_) (simp-refl Γ ρ)

[]-wk : ∀ {Γ Δ N α} (φ : Δ ⊆ N) (t : Term Γ α) (ρ : Δ ▹ Γ) →
        weaken φ (t [ ρ ]) ≡ t [ ▹-weaken Γ φ ρ ]
[]-wk φ (var ∈Γ) ρ = tk-weaken ∈Γ φ ρ

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

▹-wk-2 : ∀ {Δ E Θ} Γ (φ : Δ ⊆ E) (ψ : E ⊆ Θ) (ρ : Δ ▹ Γ) →
         ▹-weaken Γ ψ (▹-weaken Γ φ ρ) ≡ ▹-weaken Γ (⊆-trans φ ψ) ρ
▹-wk-2 ε       φ ψ ρ       = refl
▹-wk-2 (Γ ∙ α) φ ψ (t , ρ) = cong₂ _,_ (wk-tr φ ψ t) (▹-wk-2 Γ φ ψ ρ)    

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

idR : ∀ {Γ Δ} (ρ : Γ ▹ Δ) → ρ ⋆ id ≡ ρ
idR {Δ = ε}     tt      = refl
idR {Δ = Δ ∙ x} (t , ρ) =
  trans (cong (t [ id ] ,_) (idR ρ))
        (cong (_, ρ) (t[id] t))

p⋆, : ∀ {Δ Θ α} (t : Term Δ α) (γ : Δ ▹ Θ) → p ⋆ (t , γ) ≡ γ

idL : ∀ {Γ Δ} (ρ : Δ ▹ Γ) → id ⋆ ρ ≡ ρ

p⋆, {Θ = Θ} t = trans (⋆-step Θ id _ t) ∘ idL

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

idε<> : id {ε} ≡ tt
idε<> = refl

idL {ε}     tt      = refl
idL {Γ ∙ α} (t , ρ) = cong (t ,_) (p⋆, t ρ)

[]-asso : ∀ {Γ Δ Θ α} (t : Term Δ α) (γ : Γ ▹ Δ) (δ : Θ ▹ Γ) →
          t [ γ ⋆ δ ] ≡ t [ γ ] [ δ ]
[]-asso (var here) γ δ = refl
[]-asso (var (there ∈Γ)) (u , γ) δ = []-asso (var ∈Γ) γ δ            

⋆-asso : ∀ {Γ Δ Θ Λ} (γ : Δ ▹ Θ) (δ : Γ ▹ Δ) (ζ : Λ ▹ Γ) →
         (γ ⋆ δ) ⋆ ζ ≡ γ ⋆ (δ ⋆ ζ)
⋆-asso {Θ = ε} tt δ ζ = refl
⋆-asso {Θ = Θ ∙ _} (t , γ) δ ζ =
  trans (cong (_, (γ ⋆ δ) ⋆ ζ) (sym ([]-asso t δ ζ)))
        (cong (t [ δ ⋆ ζ ] ,_) (⋆-asso γ δ ζ))

maps : {Γ Δ : Ctxt Ty} {α : Ty} (t : Term Δ α) (γ : Δ ▹ Γ) (δ : Γ ▹ Δ) →
       ((t [ δ ]) , γ ⋆ δ) ≡ ((t [ δ ]) , γ ⋆ δ)
maps = λ t γ δ → refl       

TermScwf : Scwf
TermScwf = record
             { Ty       = Ty
             ; Ctx      = Ctx
             ; _,_      = _∙_
             ; ε        = ε
             ; Tm       = Term
             ; Hom      = _▹_
             ; _~_      = _≡_
             ; _~~_     = _≡_
             ; <>       = tt
             ; id       = id
             ; p        = p
             ; q        = q 
             ; _∘_      = _⋆_
             ; _[_]     = _[_]
             ; <_,_>    = flip _,_
             ; id₀      = idε<>
             ; ∘<>      = ⋆-<>
             ; varp     = id=<pq>
             ; idL      = idL
             ; idR      = idR
             ; assoc    = ⋆-asso
             ; tmId     = t[id]
             ; pCons    = p⋆,
             ; q[]      = q[]
             ; clos     = []-asso
             ; maps     = maps
             ; cong-[]  = cong-[]
             ; cong-<,> = cong-,
             ; cong-∘   = cong-⋆
             }
