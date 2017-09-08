module Unityped.TermModels where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_] ; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate ; lookup-allFin)
open import Data.Fin using (Fin ; zero ; suc ; raise ; _+_ ; fromℕ)
open import Function using (_$_ ; _∘_ ; flip)
open import Unityped.WSModel
  renaming (q to qWS ; comp to compWS ; sub to subWS ; id to idWS)
open import Relation.Binary.PropositionalEquality
open import Util
open import Iso
open import Unityped.UcwfModel
open ≡-Reasoning

-- Translation functions
toUcwf       : ∀ {n} → WellScopedTm n → UcwfTm n
toWellscoped : ∀ {n} → UcwfTm n → WellScopedTm n
homToVec     : ∀ {m n} → HomCwf m n → Vec (WellScopedTm m) n
vecToHom     : ∀ {m n} → Vec (WellScopedTm m) n → HomCwf m n

homToVec (id n)               = idSub n
homToVec (comp m n k hnk hmn) = compWS (homToVec hnk) (homToVec hmn) 
homToVec (p n)                = projSub n
homToVec (<> m)               = empt
homToVec (m , n < h , t >)    = ext (homToVec h) (toWellscoped t)

vecToHom []       = <> _
vecToHom (x ∷ xs) = _ , _ < vecToHom xs , toUcwf x >

toWellscoped (q n)         = qWS n
toWellscoped (sub m n t h) = subWS (toWellscoped t) (homToVec h)

varUcwf : ∀ {n} (i : Fin n) → UcwfTm n
varUcwf zero    = q _
varUcwf (suc i) = weaken (2ucwf (var _ i))
  where 2ucwf : ∀ {n} → WellScopedTm n → UcwfTm n
        2ucwf (var n i) = varUcwf i

toUcwf (var n i) = varUcwf i

-- left and right inverses, i.e., isomorphism

wellscoped∘ucwf : ∀ {n} (t : WellScopedTm n) → t ≡ toWellscoped (toUcwf t)
ucwf∘wellscoped : ∀ {n} (u : UcwfTm n) → u ≡ toUcwf (toWellscoped u)
ucwf-wells : ∀ {n} (u : UcwfTm n) → u U~ toUcwf (toWellscoped u)
vec∘hom : ∀ {m n} → (v : Vec (WellScopedTm m) n) → v ≡ homToVec (vecToHom v)
hom∘vec : ∀ {m n} → (h : HomCwf m n) → h ≡ vecToHom (homToVec h)

wellscoped∘ucwf (var _ zero)    = refl
wellscoped∘ucwf (var _ (suc x)) = sym $
  begin
    subWS (toWellscoped (toUcwf (var _ x))) (projSub _)
  ≡⟨ sym (cong (flip subWS (projSub _)) (wellscoped∘ucwf (var _ x))) ⟩
    subWS (var _ x) (projSub _)
  ≡⟨ refl ⟩
    lookup x (projSub _)
  ≡⟨ lookupPLemma _ x ⟩
    var (suc _) (suc x)
  ∎

ucwf-wells (q n) = reflU~ (q n)
ucwf-wells (sub n .n u (id .n)) rewrite t[id]=t (toWellscoped u)
  = transU~ (sub n n u (id n)) u (toUcwf (toWellscoped u))
    (symU~ u (sub n n u (id n)) (subId u)) (ucwf-wells u)
ucwf-wells (sub m n u (comp .m n₁ .n x x₁)) = {!!}
ucwf-wells (sub .(suc n) n u (p .n)) = {!!}
ucwf-wells (sub m .0 u (<> .m)) = {!m!}
ucwf-wells (sub m .(suc n) u (.m , n < x , x₁ >)) = {!!}

ucwf∘wellscoped (q n) = refl
ucwf∘wellscoped (sub m _ u (id _))
  rewrite t[id]=t (toWellscoped u) = sym $
    begin
      toUcwf (toWellscoped u)
    ≡⟨ sym $ ucwf∘wellscoped u ⟩
      u
    ≡⟨ {!!} ⟩ -- sub on id law proves this
      sub m m u (id m)
    ∎
ucwf∘wellscoped (sub n m u (comp _ k _ hkm hnk)) = {!!}
ucwf∘wellscoped (sub _ m u (p _)) = {!!}
ucwf∘wellscoped (sub n .0 u (<> _)) with toWellscoped u
ucwf∘wellscoped (sub n _ u (<> _)) | var .0 ()
ucwf∘wellscoped(sub n _ u (.n , k < h , x >)) = {!!}

vec∘hom [] = refl
vec∘hom (x ∷ xs)
  rewrite sym (vec∘hom xs) |
          sym (wellscoped∘ucwf x) = refl


hom∘vec (id zero) = {!!} -- id₀ axiom proves this
hom∘vec (id (suc m)) = {!!}
hom∘vec (comp m n k hnk hmn) = {!!}
hom∘vec (p n) = {!!} -- vecToHom never maps to p, 
hom∘vec (<> m) = refl
hom∘vec (m , n < h , x >)
  rewrite sym (hom∘vec h) |
          sym (ucwf∘wellscoped x) = refl

wellscoped≅ucwf : ∀ {n} → WellScopedTm n ≅ UcwfTm n
wellscoped≅ucwf =
  record { to = toUcwf
         ; from = toWellscoped
         ; inv₁ = wellscoped∘ucwf
         ; inv₂ = ucwf∘wellscoped }
