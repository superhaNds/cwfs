module ExtDepTyped.Raw.ExpSub where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product renaming (proj₁ to π₁ ; proj₂ to π₂) hiding (<_,_>)
open import Relation.Binary
open import Unityped.Ucwf
open import ExtDepTyped.Raw.PiUcwf
import Relation.Binary.Reasoning.Setoid as EqR

data Tm  : Nat → Set
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
            
  subΠ : ∀ {n m} {γ : Sub m n} {A B}
         → (Π A B) [ γ ] ~ Π (A [ γ ]) (B [ ⇑ γ ])

  subU : ∀ {m n} {γ : Sub m n} → U [ γ ] ~ U

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

cong-Πl : ∀ {n} {A A' : Tm n} {B} → A ~ A' → Π A B ~ Π A' B
cong-Πl A~A' = cong-Π A~A' refl~

cong-Πr : ∀ {n} {B B' : Tm (suc n)} {A} → B ~ B' → Π A B ~ Π A B'
cong-Πr B~B' = cong-Π refl~ B~B'

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

ter-arrow : ∀ {m} (γ : Sub m 0) → γ ≈ <>
ter-arrow γ = begin
  γ           ≈⟨ sym≈ idL ⟩
  id {0} ∘ γ  ≈⟨ cong-∘₁ id-zero ⟩
  <> ∘ γ      ≈⟨ left-zero ⟩
  <>
  ∎
  where open EqR (SubSetoid {_} {_})

-- lifting distributes over composition

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

ExpSubUcwf : Ucwf
ExpSubUcwf = record
               { Tm       = Tm
               ; Sub      = Sub
               ; _~_      = _~_
               ; _≈_      = _≈_
               ; IsEquivT =
                   record { refl  = refl~
                          ; sym   = sym~
                          ; trans = trans~ }
               ; IsEquivS =
                   record { refl  = refl≈
                          ; sym   = sym≈
                          ; trans = trans≈ }
               ; id        = id
               ; _∘_       = _∘_
               ; _[_]      = _[_]
               ; <>        = <>
               ; <_,_>     = <_,_>
               ; p         = p
               ; q         = q
               ; id-zero   = id-zero
               ; left-zero = left-zero
               ; idExt     = idExt
               ; idL       = idL
               ; idR       = idR
               ; assoc     = ∘-asso
               ; subId     = subId
               ; pCons     = p-∘
               ; qCons     = q-sub
               ; subComp   = subComp
               ; compExt   = compExt
               ; cong-<,>  = cong-<,>
               ; cong-sub  = cong-sub
               ; cong-∘    = cong-∘
               }

ExpSubLamUcwf : λβη-ucwf
ExpSubLamUcwf = record
                  { ucwf     = ExpSubUcwf
                  ; lam      = ƛ
                  ; app      = app
                  ; subApp   = subApp
                  ; subLam   = subLam
                  ; β        = β
                  ; η        = η
                  ; cong-lam = cong-lam
                  ; cong-app = cong-app
                  }

ExpSubΠUcwf : Π-λβη-ucwf
ExpSubΠUcwf = record
                { λucwf  = ExpSubLamUcwf
                ; Π      = Π
                ; U      = U
                ; subU   = subU
                ; subΠ   = subΠ
                ; cong-Π = cong-Π
                }
