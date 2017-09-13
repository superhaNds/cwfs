module Unityped.TermModels where

open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; [_] ; tabulate ; tail)
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

toUcwf (var _ zero)    = q _
toUcwf (var _ (suc i)) = weaken (toUcwf (var _ i))

-- Inverses
wellscoped∘ucwf : ∀ {n} (t : WellScopedTm n) → t ≡ toWellscoped (toUcwf t)
vec∘hom : ∀ {m n} → (v : Vec (WellScopedTm m) n) → v ≡ homToVec (vecToHom v)
ucwf∘wellscoped : ∀ {n} (u : UcwfTm n) → u ~ₜ toUcwf (toWellscoped u)
hom∘vec : ∀ {n m} (u : HomCwf m n) → u ~ₕ vecToHom (homToVec u)

wellscoped∘ucwf (var _ zero)    = refl
wellscoped∘ucwf (var _ (suc x)) = sym $
  begin
    subWS (toWellscoped $ toUcwf (var _ x)) (projSub _)
  ≡⟨ sym $ cong (flip subWS (projSub _)) (wellscoped∘ucwf (var _ x)) ⟩
    subWS (var _ x) (projSub _)
  ≡⟨ refl ⟩
    lookup x (projSub _)
  ≡⟨ lookupPLemma _ x ⟩
    var (suc _) (suc x)
  ∎ where open ≡-Reasoning

lemma2q : ∀ {n} (u : UcwfTm (suc n)) → toWellscoped u ≡ qWS _
               → (toUcwf (toWellscoped u)) ~ₜ q _
lemma2q u pr rewrite pr = refl~ₜ

ucwf∘wellscoped (q n) = refl~ₜ

ucwf∘wellscoped (sub n _ u (id _))
  rewrite t[id]=t (toWellscoped u)
    = trans~ₜ (sym~ₜ (subId u)) (ucwf∘wellscoped u)

ucwf∘wellscoped (sub m n u (comp _ k _ x y)) = {!!}
  where open EqR (UcwfTmS {m})

ucwf∘wellscoped (sub .(suc n) n u (p .n)) with toWellscoped u
                                             | inspect toWellscoped u
ucwf∘wellscoped (sub .(suc n) n u (p .n)) | var .n x | [ var=u ] = sym~ₜ $
  begin
    toUcwf (subWS (var _ x) (projSub _))
  ≈⟨ help n x u var=u ⟩
    weaken (toUcwf $ toWellscoped u)
  ≈⟨ sym~ₜ $ cong~ₜ weaken (ucwf∘wellscoped u) ⟩
    weaken u
  ≈⟨ refl~ₜ ⟩
    sub (suc n) n u (p n)
  ∎ where open EqR (UcwfTmS {_})
          open Reveal_·_is_
          help : ∀ n x u → toWellscoped u ≡ var n x →
                   toUcwf (subWS (var n x) (projSub n))
                   ~ₜ weaken (toUcwf $ toWellscoped u)
          help n x u l rewrite subPLift (var n x)
                              | liftVar n x
                              | l = refl~ₜ
                                          
ucwf∘wellscoped (sub m .0 u (<> .m)) with toWellscoped u
ucwf∘wellscoped (sub m _ u (<> .m)) | var .0 ()

ucwf∘wellscoped (sub m _ u (_ , n < xs , x >)) with toWellscoped u
                                                  | inspect toWellscoped u
ucwf∘wellscoped (sub m .(suc n) u (.m , n < xs , x′ >))
  | var .(suc n) zero | [ q=2WSu ] = begin
     sub m (suc n) u (m , n < xs , x′ >)
   ≈⟨ cong~ₜ (λ a → sub _ _ a (m , n < xs , x′ >)) (ucwf∘wellscoped u) ⟩
     sub m (suc n) (toUcwf (toWellscoped u)) (m , n < xs , x′ >)
   ≈⟨ cong~ₜ (λ a → sub _ _ a (_ , _ < xs , x′ >)) (lemma2q u q=2WSu) ⟩
     sub m (suc n) (q _) (m , n < xs , x′ >)
   ≈⟨ sym~ₜ (q[<a,t>] x′ xs) ⟩
     x′
   ≈⟨ ucwf∘wellscoped x′ ⟩
     toUcwf (toWellscoped x′)
   ∎ where open EqR (UcwfTmS {_})
           open Reveal_·_is_
ucwf∘wellscoped (sub m _ u (.m , n < xs , x′ >))
  | var _ (suc x) | [ var=u ] = {!!}
  where open Reveal_·_is_

vec∘hom [] = refl
vec∘hom (x ∷ xs)
  rewrite sym (vec∘hom xs) |
          sym (wellscoped∘ucwf x) = refl

hom∘vec (id zero)    = id₀
hom∘vec (id (suc m)) = 
  begin
    id (suc m)
  ≈⟨ id<p,q> ⟩
    _ , _ < p _ , q _ >
  ≈⟨ cong~ₕ (λ x → _ , _ < x , q _ >) (hom∘vec $ p m) ⟩
    _ , _ < vecToHom (projSub m) , q _ >
  ≈⟨ help m ⟩
    _ , _ < vecToHom $ tail (idSub _) , q _ >
  ∎ where open EqR (HomCwfS {suc m} {suc m})
          help : ∀ m → suc m , m < vecToHom (projSub m) , q m >
                  ~ₕ suc m , m < vecToHom (tail $ idSub _) , q m >
          help m rewrite tailIdp m = refl~ₕ

hom∘vec (comp m n k hnk hmn) with homToVec hnk | inspect homToVec hnk
hom∘vec (comp m n .0 hnk hmn) | [] | [ eq ] = {!!}
hom∘vec (comp m n₁ _ hnk hmn) | x ∷ a | [ eq ] = {!!}
  where open Reveal_·_is_
  
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
