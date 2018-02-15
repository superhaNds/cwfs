module Ext-Typed.DTyped.LamPiSubTy where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat renaming (ℕ to Nat)
open import Data.Product hiding (_,_)
open import Data.Star using (Star; ε; _◅_)
open import Data.Unit
open import Function as F using (_$_)
open import Data.Vec as Vec hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Ext-Typed.DTyped.LamPiSub
