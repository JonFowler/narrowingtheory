module STLC.Semantics where

open import Helpful
open import STLC.Exp
open import Data.Vec
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Sum
open import Data.Unit
open import Function
open import Coinduction

--data FinSet : Set where
--  ∅ : FinSet
--  one : FinSet
--  _⊕_ : FinSet → FinSet → FinSet
--  
--data FinVar : FinSet → Set where
--  here : FinVar one
--  inL : {X Y : FinSet} → FinVar X → FinVar (X ⊕ Y)
--  inR : {X Y : FinSet} → FinVar Y → FinVar (X ⊕ Y)
 

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

                     

data narrSet {n : ℕ}{Γ : Cxt n} : {t : Type}{X : VarSet} → (Exp X Γ t) → Set₁ where
   inL : ∀{t u}(x : Unit) → narrSet (inL {t = t}{u} (fvar [] x))
   inR : ∀{t u}(x : Unit) → narrSet (inR {t = t}{u} (fvar [] x ))
   var : ∀{t}{X : VarSet}(v : Var Γ t) → narrSet {X = X} (var v)
   case : ∀{t u v}{X : VarSet}{e : Exp X Γ (u ⊕ v)} →  narrSet e →  
                               narrSet {t = t}{X = λ Γ t → X Γ t ⊎ (Unit ⊎ Unit)} 
                                       (case (e >>=ₛ (λ x → fvar [] (inj₁ x))) 
                                       (fvar [] (inj₂ (inj₁ unit)))
                                       (fvar [] (inj₂ (inj₂ unit))))
