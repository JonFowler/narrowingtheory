module STLC.Semantics where

open import Helpful
open import STLC.Exp
open import Data.Vec
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Sum

data _⇒R_ {X : VarSet}{n : ℕ}{Γ : Cxt n}{t : Type} : 
          Exp X Γ t → Exp X Γ t → Set where
   caseinL : ∀{u v} → (e : Exp X Γ u) → (e₁ : Exp X (u ∷ Γ) t) → (e₂ : Exp X (v ∷ Γ) t)
             → case (inL e) e₁ e₂ ⇒R e₁ ⟨ₛ e ⟩
   caseinR : ∀{u v} → (e : Exp X Γ v) → (e₁ : Exp X (u ∷ Γ) t) → (e₂ : Exp X (v ∷ Γ) t)
             → case (inR e) e₁ e₂ ⇒R e₂ ⟨ₛ e ⟩

data _⇒_ {X : VarSet}{n : ℕ}{Γ : Cxt n}{t : Type} : 
          Exp X Γ t → Exp X Γ t → Set where
   redex : ∀{e e'} → e ⇒R e' → e ⇒ e'
   prom-subj : ∀{u v}{e e' : Exp X Γ (u ⊕ v)}{e₁ : Exp X (u ∷ Γ) t}{e₂ : Exp X (v ∷ Γ) t} →
                     e ⇒ e' → case e e₁ e₂ ⇒ case e' e₁ e₂

                     

