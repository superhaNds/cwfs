module ExtDepTyped.ImpSubTy where

open import Function as F using (_$_ ; flip)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_] ; lookup)
open import Data.Vec.Relation.Unary.All.Properties using (gmap)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import ExtDepTyped.Raw.ImpSub
open import Unityped.ImpSub as Ren using (Ren ; lookup)

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _∙_ : ∀ {n} → Ctx n → Tm n → Ctx (1 + n)

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _⊢_∈s_

data _⊢     : ∀ {n} (Γ : Ctx n) → Set

data _⊢_    : ∀ {n} (Γ : Ctx n) (A : Tm n) → Set

data _⊢_∈_  : ∀ {n} (Γ : Ctx n) (t A : Tm n) → Set

data _⊢_∈s_ : ∀ {m n} → Ctx n → Sub m n → Ctx m → Set

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

  ty-var₀ : ∀ {n} {Γ : Ctx n} {A : Tm n}
            → Γ ⊢ A
            → Γ ∙ A ⊢ var zero ∈ weaken A

  ty-varₙ : ∀ {n} {Γ : Ctx n} {i : Fin n} {A B}
            → Γ ⊢ B
            → Γ ⊢ var i ∈ A
            → Γ ∙ B ⊢ var (suc i) ∈ weaken A

  ty-app : ∀ {n} {Γ : Ctx n} {f t A B}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ f ∈ Π A B
           → Γ ⊢ t ∈ A
           → Γ ⊢ app f t ∈ B [ id , t ]
           
  ty-Π-I : ∀ {n} {Γ : Ctx n} {A B t}
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ∙ A ⊢ t ∈ B
           → Γ ⊢ ƛ t ∈ Π A B

data _⊢_∈s_ where

  ⊢<> : ∀ {n} {Γ : Ctx n}
        → Γ ⊢
        → ⋄ ⊢ [] ∈s Γ

  ⊢<,> : ∀ {m n Δ Γ A t} {γ : Sub m n}
         → Γ ⊢ γ ∈s Δ
         → Γ ⊢ A
         → Δ ⊢ t ∈ A [ γ ]
         → Γ ∙ A ⊢ (γ , t) ∈s Δ

ty-of : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ A → Tm n
ty-of {A = A} _ = A

tm-of : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Tm n
tm-of {t = t} _ = t

ty-of' : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Tm n
ty-of' {A = A} _ = A

dom : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ} → Γ ⊢ γ ∈s Δ → Ctx n
dom {Γ = Γ} _ = Γ

cod : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {γ} → Γ ⊢ γ ∈s Δ → Ctx m
cod {Δ = Δ} _ = Δ

wf⁻¹ : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢
wf⁻¹ (c-ext Γ⊢ _) = Γ⊢

wf⁻² : ∀ {n} {Γ : Ctx n} {A} → Γ ∙ A ⊢ → Γ ⊢ A
wf⁻² (c-ext _ ⊢A) = ⊢A

wfTy-wf : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢ A
          → Γ ⊢
            
wfTm-wf : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ∈ A → Γ ⊢
wfTm-wf (ty-var₀ ⊢A)      = c-ext (wfTy-wf ⊢A) ⊢A
wfTm-wf (ty-varₙ ⊢B ⊢i)   = c-ext (wfTm-wf ⊢i) ⊢B
wfTm-wf (ty-app _ _ _ ⊢t) = wfTm-wf ⊢t
wfTm-wf (ty-Π-I ⊢A _ ⊢t)  = wf⁻¹ $ wfTm-wf ⊢t

wfSub-wf₁ : ∀ {m n Γ Δ} {γ : Sub m n} → Γ ⊢ γ ∈s Δ → Δ ⊢
wfSub-wf₁ (⊢<> Δ⊢)      = Δ⊢
wfSub-wf₁ (⊢<,> ⊢γ _ _) = wfSub-wf₁ ⊢γ

wfSub-wf₂ : ∀ {m n Γ Δ} {γ : Sub m n} → Γ ⊢ γ ∈s Δ → Γ ⊢
wfSub-wf₂ (⊢<> _)        = c-emp
wfSub-wf₂ (⊢<,> ⊢γ ⊢A _) = c-ext (wfSub-wf₂ ⊢γ) ⊢A

wfTy-wf (ty-U Γ⊢)     = Γ⊢
wfTy-wf (ty-∈U ⊢A)    = wfTm-wf ⊢A
wfTy-wf (ty-Π-F ⊢A _) = wfTy-wf ⊢A

ty-q : ∀ {n} {Γ : Ctx n} {A}
       → Γ ⊢ A
       → (Γ ∙ A) ⊢ q ∈ (A [ p ])
ty-q {A = A} ⊢A rewrite sym $ wk-sub-p {t = A} = ty-var₀ ⊢A

subst' : ∀ {A : Set} {a a'} {C : A → Set} → a ≡ a' → C a → C a'
subst' refl C = C

module Var where

  sucs-lemma : ∀ {m n Δ A i} (ρ : Ren m n)
               → Δ ⊢ var (suc i) ∈ (weaken $ A [ map var ρ ])
               → Δ ⊢ var (suc i) ∈ (A [ map var (map suc ρ) ])
  sucs-lemma {A = A} ρ ⊢i rewrite weaken-map-var A ρ = ⊢i

  map-suc-preserv : ∀ {m n Γ Δ A} (ρ : Ren m n)
                    → Δ ⊢ A
                    → Γ ⊢ map var ρ ∈s Δ
                    → Γ ⊢ map var (map suc ρ) ∈s Δ ∙ A
  map-suc-preserv []      ⊢A (⊢<> Δ⊢)        = ⊢<> (c-ext Δ⊢ ⊢A)
  map-suc-preserv (x ∷ ρ) ⊢B (⊢<,> ⊢ρ ⊢A ⊢x) = ⊢<,> (map-suc-preserv ρ ⊢B ⊢ρ) ⊢A (sucs-lemma {A = ty-of ⊢A} ρ (ty-varₙ ⊢B ⊢x))

  id-preserv : ∀ {n} {Γ : Ctx n}
               → Γ ⊢
               → Γ ⊢ id ∈s Γ
  id-preserv {Γ = ⋄}     c-emp         = ⊢<> c-emp
  id-preserv {Γ = Γ ∙ A} (c-ext Γ⊢ ⊢A) = ⊢<,> (map-suc-preserv Ren.id ⊢A (id-preserv Γ⊢)) ⊢A (ty-q ⊢A)

  p-preserv : ∀ {n} {Γ : Ctx n} {A}
              → Γ ⊢ A
              → Γ ⊢ p ∈s (Γ ∙ A)
  p-preserv ⊢A = map-suc-preserv Ren.id ⊢A (id-preserv (wfTy-wf ⊢A))  

  ↑-preserv : ∀ {m n Γ Δ A} {ρ : Ren m n}
              → Γ ⊢ A
              → Δ ⊢ A [ map var ρ ]
              → Γ ⊢ map var ρ ∈s Δ
              → Γ ∙ A ⊢ map var (Ren.↑ ρ) ∈s Δ ∙ (A [ map var ρ ])
  ↑-preserv {Δ = Δ} {A} {ρ = ρ} ⊢A ⊢A[ρ] ⊢ρ
    = ⊢<,> (map-suc-preserv ρ ⊢A[ρ] ⊢ρ) ⊢A (subst' {a = weaken (A [ map var ρ ])}
                                                   {A [ map var (map suc ρ) ]}
                                                   {Δ ∙ (A [ map var ρ ]) ⊢ q ∈_}
                                                   (trans (weaken-map-wk A (map var ρ))
                                                          (cong (A [_]) (map-var-weaken ρ)))
                                                   (ty-var₀ ⊢A[ρ]))

  var-ty-lemma : ∀ {m n x i A Δ} {ρ : Ren m n}
                 → Δ ⊢ x ∈ A [ map var ρ ]
                 → Δ ⊢ x ∈ (weaken A) [ map var (i ∷ ρ) ]
  var-ty-lemma {i = i} {A = A} {ρ = ρ} hyp
    rewrite weaken-sub-ext (var i) A (map var ρ) = hyp

  sub-ty-pr' : ∀ {m n Γ Δ A} {ρ : Ren m n}
               → Γ ⊢ A
               → Γ ⊢ map var ρ ∈s Δ
               → Δ ⊢ A [ map var ρ ]
  
  sub-tm-pr' : ∀ {m n Γ Δ A t} {ρ : Ren m n}
               → Γ ⊢ t ∈ A
               → Γ ⊢ map var ρ ∈s Δ
               → Δ ⊢ t [ map var ρ ] ∈ A [ map var ρ ]

  sub-ty-pr' (ty-U _)   ⊢ρ = ty-U (wfSub-wf₁ ⊢ρ)
  sub-ty-pr' (ty-∈U ⊢A) ⊢ρ = ty-∈U (sub-tm-pr' ⊢A ⊢ρ)
  sub-ty-pr' {m = m} {n} {Δ = Δ} {ρ = ρ} (ty-Π-F {A = A} {B} ⊢A ⊢B) ⊢ρ
    = ty-Π-F (sub-ty-pr' ⊢A ⊢ρ) (subst' {a = map var (Ren.↑ ρ)} {↑ (map var ρ)}
                                        {λ x → (Δ ∙ (A [ map var ρ ])) ⊢ (B [ x ])}
                                        (sym $ ↑-map-var ρ)
                                        (sub-ty-pr' ⊢B (↑-preserv ⊢A (sub-ty-pr' ⊢A ⊢ρ) ⊢ρ)))
    
  sub-tm-pr' {ρ = x ∷ ρ} (ty-var₀ _)    (⊢<,> ⊢ρ ⊢A ⊢x) = var-ty-lemma {A = ty-of ⊢A} ⊢x
  sub-tm-pr' {ρ = x ∷ ρ} (ty-varₙ _ ⊢i) (⊢<,> ⊢ρ ⊢B ⊢x) = var-ty-lemma {i = x} {ty-of' ⊢i} $ sub-tm-pr' ⊢i ⊢ρ 
  sub-tm-pr' {Δ = Δ} {ρ = ρ} (ty-app {A = A} {B} ⊢A ⊢B ⊢f ⊢t) ⊢ρ
    rewrite prop-β {σ = map var ρ} {t = tm-of ⊢t} {B = ty-of ⊢B}
      = ty-app (sub-ty-pr' ⊢A ⊢ρ)
               (subst' {a = map var (Ren.↑ ρ)} {↑ (map var ρ)}
                       {λ x → Δ ∙ (A [ map var ρ ]) ⊢ B [ x ]}
                       (sym $ ↑-map-var ρ)
                       (sub-ty-pr' ⊢B $ ↑-preserv ⊢A (sub-ty-pr' ⊢A ⊢ρ) ⊢ρ))
               (sub-tm-pr' ⊢f ⊢ρ)
               (sub-tm-pr' ⊢t ⊢ρ) 
  sub-tm-pr' {Δ = Δ} {ρ = ρ} (ty-Π-I {A = A} {B} {t = t} ⊢A ⊢B ⊢t) ⊢ρ
    = ty-Π-I (sub-ty-pr' ⊢A ⊢ρ)
             (subst' {a = map var (Ren.↑ ρ)} {↑ (map var ρ)}
                     {λ x → Δ ∙ (A [ map var ρ ]) ⊢ B [ x ]}
                     (sym $ ↑-map-var ρ)
                     (sub-ty-pr' ⊢B $ ↑-preserv ⊢A (sub-ty-pr' ⊢A ⊢ρ) ⊢ρ))
             (subst' {a = map var (Ren.↑ ρ)} {↑ (map var ρ)}
                     {λ x → Δ ∙ (A [ map var ρ ]) ⊢ t [ x ] ∈ B [ x ]}
                     (sym $ ↑-map-var ρ)
                     (sub-tm-pr' ⊢t $ ↑-preserv ⊢A (sub-ty-pr' ⊢A ⊢ρ) ⊢ρ))

  sub-ty-pr : ∀ {m n Γ Δ A} {ρ : Ren m n}
              → Γ ⊢ A
              → Γ ⊢ map var ρ ∈s Δ
              → Δ ⊢ A / ρ
  sub-ty-pr {A = A} {ρ} ⊢A ⊢ρ
    rewrite /-map-var ρ A = sub-ty-pr' ⊢A ⊢ρ

  sub-tm-pr : ∀ {m n Γ Δ A t} {ρ : Ren m n}
              → Γ ⊢ t ∈ A
              → Γ ⊢ map var ρ ∈s Δ
              → Δ ⊢ t / ρ ∈ (A / ρ)
  sub-tm-pr {A = A} {t} {ρ} ⊢t ⊢ρ
    rewrite /-map-var ρ t
          | /-map-var ρ A = sub-tm-pr' ⊢t ⊢ρ

weaken-ty-preserv : ∀ {n} {Γ : Ctx n} {A B}
                    → Γ ⊢ A
                    → Γ ⊢ B
                    → Γ ∙ A ⊢ weaken B
weaken-ty-preserv ⊢A ⊢B = Var.sub-ty-pr ⊢B (Var.p-preserv ⊢A)

weaken-tm-preserv : ∀ {n Γ A B} {t : Tm n}
                    → Γ ⊢ A  
                    → Γ ⊢ t ∈ B
                    → Γ ∙ A ⊢ weaken t ∈ weaken B
weaken-tm-preserv ⊢A ⊢t = Var.sub-tm-pr ⊢t (Var.p-preserv ⊢A)

conv : ∀ {n} {Γ : Ctx n} {t A A'}
       → Γ ⊢ A'
       → Γ ⊢ t ∈ A
       → A' ≡ A
       → Γ ⊢ t ∈ A'
conv _ t∈A refl = t∈A 

map-wk-preserv : ∀ {m n Γ Δ A} {γ : Sub m n}
                 → Δ ⊢ A
                 → Γ ⊢ γ ∈s Δ
                 → Γ ⊢ map weaken γ ∈s (Δ ∙ A)
map-wk-preserv {γ = []} ⊢A (⊢<> ⊢Δ) = ⊢<> (c-ext ⊢Δ ⊢A)
map-wk-preserv {Δ = Δ} {γ = x ∷ γ} Δ⊢A' (⊢<,> {A = A} ⊢γ Γ⊢A ⊢x)
  = ⊢<,> (map-wk-preserv Δ⊢A' ⊢γ) Γ⊢A (subst' {a = weaken (A [ γ ])}
                                              {A [ map weaken γ ]}
                                              {Δ ∙ (ty-of Δ⊢A') ⊢ weaken x ∈_}
                                              (weaken-map-wk A γ)
                                              (weaken-tm-preserv Δ⊢A' ⊢x))

↑-preserves : ∀ {m n Γ Δ A} {γ : Sub m n}
              → Γ ⊢ A
              → Δ ⊢ A [ γ ]
              → Γ ⊢ γ ∈s Δ
              → Γ ∙ A ⊢ ↑ γ ∈s (Δ ∙ (A [ γ ]))
↑-preserves {Δ = Δ} {A} {γ} ⊢A ⊢A[γ] ⊢γ
  = ⊢<,> (map-wk-preserv ⊢A[γ] ⊢γ) ⊢A (subst' {a = weaken (A [ γ ])}
                                              {A [ map weaken γ ]}
                                              {Δ ∙ (A [ γ ]) ⊢ q ∈_}
                                              (weaken-map-wk A γ)
                                              (ty-var₀ ⊢A[γ]))

subst-ty : ∀ {m n Γ Δ A} {γ : Sub m n}
           → Γ ⊢ A
           → Γ ⊢ γ ∈s Δ
           → Δ ⊢ A [ γ ]

subst-tm : ∀ {m n Γ Δ A t} {γ : Sub m n}
           → Γ ⊢ t ∈ A
           → Γ ⊢ γ ∈s Δ
           → Δ ⊢ t [ γ ] ∈ A [ γ ]    

subst-tm {γ = x ∷ γ} (ty-var₀ {A = A} ⊢A) (⊢<,> ⊢γ _ ⊢x)
  rewrite weaken-sub-ext x A γ = ⊢x 
subst-tm {γ = x ∷ γ} (ty-varₙ {i = i} {A} ⊢B ⊢t) (⊢<,> ⊢γ _ _)
  rewrite weaken-sub-ext x A γ = subst-tm ⊢t ⊢γ
subst-tm {Δ = Δ} {γ = γ} (ty-app {f = f} {t} {A} {B} ⊢A ⊢B ⊢f ⊢t) ⊢γ
  rewrite prop-β {σ = γ} {t} {B}
    = ty-app (subst-ty ⊢A ⊢γ)
             (subst-ty ⊢B $ ↑-preserves ⊢A (subst-ty ⊢A ⊢γ) ⊢γ) 
             (subst-tm ⊢f ⊢γ)
             (subst-tm ⊢t ⊢γ)
subst-tm (ty-Π-I ⊢A ⊢B ⊢t) ⊢γ
  = ty-Π-I (subst-ty ⊢A ⊢γ)
           (subst-ty ⊢B $ ↑-preserves ⊢A (subst-ty ⊢A ⊢γ) ⊢γ)
           (subst-tm ⊢t $ ↑-preserves ⊢A (subst-ty ⊢A ⊢γ) ⊢γ)

subst-ty (ty-U Γ⊢)      ⊢γ = ty-U (wfSub-wf₁ ⊢γ)
subst-ty (ty-∈U ⊢A)     ⊢γ = ty-∈U (subst-tm ⊢A ⊢γ)
subst-ty (ty-Π-F ⊢A ⊢B) ⊢γ = ty-Π-F (subst-ty ⊢A ⊢γ) (subst-ty ⊢B $ ↑-preserves ⊢A (subst-ty ⊢A ⊢γ) ⊢γ)

∘-preserv : ∀ {m n k Γ Δ Θ} {γ₁ : Sub n k} {γ₂ : Sub m n}
            → Θ ⊢ γ₁ ∈s Δ
            → Δ ⊢ γ₂ ∈s Γ
            → Θ ⊢ γ₁ ∘ γ₂ ∈s Γ
∘-preserv (⊢<> _) ⊢γ₂ = ⊢<> (wfSub-wf₁ ⊢γ₂)
∘-preserv {Γ = Γ} {Δ} {Θ = Θ ∙ B} {x ∷ γ₁} {γ₂} (⊢<,> ⊢γ₁ ⊢A ⊢t) ⊢γ₂
  = ⊢<,> (∘-preserv ⊢γ₁ ⊢γ₂) ⊢A
         (subst' {a = B [ γ₁ ] [ γ₂ ]}
                 {B [ γ₁ ∘ γ₂ ]}
                 {Γ ⊢ x [ γ₂ ] ∈_}
                 (sym $ subComp B)
                 (subst-tm ⊢t ⊢γ₂))               

wfTm-wfTy : ∀ {n} {Γ : Ctx n} {t A}
            → Γ ⊢ t ∈ A
            → Γ ⊢ A
wfTm-wfTy (ty-var₀ ⊢A)     = weaken-ty-preserv ⊢A ⊢A
wfTm-wfTy (ty-varₙ ⊢B ⊢t)  = weaken-ty-preserv ⊢B (wfTm-wfTy ⊢t)
wfTm-wfTy (ty-Π-I ⊢A ⊢B _) = ty-Π-F ⊢A ⊢B
wfTm-wfTy {Γ = Γ} (ty-app {t = t} {A = A} ⊢A ⊢B ⊢f ⊢t) =
  let ⊢id = Var.id-preserv (wfTy-wf ⊢A)
  in subst-ty ⊢B (⊢<,> (Var.id-preserv (wfSub-wf₁ ⊢id)) ⊢A
                       (subst' {a = A} {A [ id ]} {Γ ⊢ t ∈_} (sym $ subId) ⊢t))
