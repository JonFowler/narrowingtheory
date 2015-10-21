module Helpful where

open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality


∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
     (C : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ C = ∃ λ a → ∃ λ b → ∃ λ c → C a b c

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl
