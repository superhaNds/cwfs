module Unityped.Wellscoped.Typed.CtxType where

open import Data.Nat

data Ty : Set where
  o : Ty

data Ctx : ℕ →  Set where
  ε   : Ctx 0
  _,_ : {n : ℕ} → Ctx n → Ty → Ctx (suc n)
