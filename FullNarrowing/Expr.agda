module Expr where

open import Helpful
open import Subs

open import Data.Nat
open import Data.Vec

data Ty : Set where
  Nat : Ty
  _→ₜ_ : Ty → Ty → Ty

Cxt : ℕ → Set
Cxt = Vec Ty


data Expr {V : ℕ} (Γ : Cxt V) (X : VarSet) : Ty → Set where
  
