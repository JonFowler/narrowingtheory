module Expr where

open import Data.Nat


data Ty : Set where
  Nat : Ty
  _→ₜ_ : Ty → Ty → Ty
