module Helpful where

open import Data.Product
open import Level

∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
     (C : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ C = ∃ λ a → ∃ λ b → ∃ λ c → C a b c


