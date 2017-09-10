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
import Relation.Binary.EqReasoning as EqR

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

-- Inverses
wellscoped∘ucwf : ∀ {n} (t : WellScopedTm n) → t ≡ toWellscoped (toUcwf t)
vec∘hom : ∀ {m n} → (v : Vec (WellScopedTm m) n) → v ≡ homToVec (vecToHom v)
ucwf∘wellscoped : ∀ {n} (u : UcwfTm n) → u ~ₜ toUcwf (toWellscoped u)
hom∘vec : ∀ {n m} (u : HomCwf m n) → u ~ₕ vecToHom (homToVec u)

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
  ∎ where open ≡-Reasoning

-- q case
ucwf∘wellscoped (q n) = refl~ₜ

-- id case
ucwf∘wellscoped (sub n _ u (id _))
  rewrite t[id]=t (toWellscoped u)
    = trans~ₜ (sym~ₜ (subId u)) (ucwf∘wellscoped u)

-- composition case
ucwf∘wellscoped (sub m n u (comp _ k _ x y)) = begin
    (sub m n u (comp m k n x y))
  ≈⟨ refl~ₜ ⟩
    sub _ _ u (comp _ _ _ x y)
  ≈⟨ ∘sub u x y ⟩
    sub _ _ (sub _ _ u x) y
  ≈⟨ {!!} ⟩
    {!!}
    
  ∎
  where open EqR (UcwfTmS {m})

-- p case
ucwf∘wellscoped (sub .(suc n) n u (p .n)) = {!!}

ucwf∘wellscoped (sub m .0 u (<> .m)) with toWellscoped u
ucwf∘wellscoped (sub m _ u (<> .m)) | var .0 ()
ucwf∘wellscoped (sub m _ u (_ , n < xs , x >)) = {!!}

vec∘hom [] = refl
vec∘hom (x ∷ xs)
  rewrite sym (vec∘hom xs) |
          sym (wellscoped∘ucwf x) = refl

hom∘vec (id zero) = id₀
hom∘vec (id (suc m)) = {!!}
hom∘vec (comp m n k hnk hmn) = {!!}
hom∘vec (p n) = {!!}
hom∘vec (<> m) = refl~ₕ
hom∘vec (m , n < u , x >) = sym~ₕ $
  begin
    m , n < vecToHom (homToVec u) , toUcwf (toWellscoped x) >
  ≈⟨ sym~ₕ $ cong~ₕ (λ a → m , n < a , toUcwf (toWellscoped x) >) (hom∘vec u) ⟩
    m , n < u , toUcwf (toWellscoped x) >
  ≈⟨ sym~ₕ $ congt~ₕ (λ a → m , n < u , a >) (ucwf∘wellscoped x) ⟩
    (m , n < u , x >)
  ∎ where open EqR (HomCwfS {suc n} {m})

