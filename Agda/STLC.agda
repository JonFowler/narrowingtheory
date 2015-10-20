module STLC where

open import Data.Vec
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Sum

data Type : Set where
  V1 : Type 
  _⊕_ : Type → Type → Type
  
Cxt : ℕ → Set
Cxt n = Vec Type n

Cxt+ : Set
Cxt+ = ∃ (λ n → Cxt n)

VarSet : Set₁
VarSet = {n : ℕ} → Cxt n → Type → Set

Var : VarSet
Var [] t = ⊥
Var (t ∷ Γ) t₁ = t ≡ t₁ ⊎ Var Γ t₁

data Val {n : ℕ} (X : VarSet) (Γ : Cxt n)  : Type → Set₁

data _⊆_ : {n n' : ℕ} → (Γ' : Cxt n') → (Γ : Cxt n) → Set where
  weak : ∀{n}{Γ : Cxt n} → (u : Type) → Γ ⊆ (u ∷ Γ)
--  exchange : ∀{n}{Γ : Cxt n} → (u t : Type) → (u ∷ t ∷ Γ) ⊆ (t ∷ u ∷ Γ)
--  lift : ∀ {u n n'}{Γ : Cxt n}{Γ' : Cxt n'} → Γ ⊆ Γ'
              --→ (u ∷ Γ) ⊆ (u ∷ Γ')

data Exp (X : VarSet) {n : ℕ} (Γ : Cxt n) (t : Type) : Set₁ where
   val : (a : Val X Γ t) → Exp X Γ t
   case : ∀{u v} → Exp X Γ (u ⊕ v) → 
                    Exp X (u ∷ Γ) t → 
                    Exp X (v ∷ Γ) t → 
                    Exp X Γ t
                    
   var : (v : Var Γ t) → Exp X Γ t
   fvar : (x : X Γ t) → Exp X Γ t
   weak : ∀{u n'}{Γ' : Cxt n'} → Exp X Γ' t → 
                           (_≡_ {A = Cxt+} (n , Γ) (suc n' , u ∷ Γ')) 
                           → Exp X Γ t
   
data Val {n : ℕ} (X : VarSet) (Γ : Cxt n)  where
   unit : Val X Γ V1
   inL : ∀{t u} (e : Exp X Γ t) → Val X Γ (t ⊕ u) 
   inR : ∀{t u} (e : Exp X Γ u) → Val X Γ (t ⊕ u) 

   
replaceV : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
        Val X (Γ ++ u ∷ Γ') t → Exp X Γ' u → Val X (Γ ++ Γ') t


--tagExp : ∀{s s' t}{Γ' : Cxt s'}{X : VarSet} → (Γ : Cxt s) → (n : ℕ) → 
--                      Exp X (Γ ++ Γ') t → Exp X (Γ ++ tag n Γ') t
--
--tagVal : ∀{s s' t}{Γ' : Cxt s'}{X : VarSet} → (Γ : Cxt s) → (n : ℕ) → 
--                Val X (Γ ++ Γ') t → Val  X (Γ ++ tag n Γ') t
--tagVal Γ n unit = unit
--tagVal Γ n (inL e) = inL (tagExp Γ n e)
--tagVal Γ n (inR e) = inR (tagExp Γ n e)
--
--tagVar : ∀{s s' t}{Γ' : Cxt s'} → (Γ : Cxt s) → (n : ℕ) → 
--        Var (Γ ++ Γ') t → Var (Γ ++ tag n Γ') t
--tagVar [] n v = v
--tagVar (t ∷ Γ) n (inj₁ refl) = inj₁ refl
--tagVar (t₁ ∷ Γ) n (inj₂ y) = inj₂ (tagVar Γ n y)
--tagVar (tag n Γ) n₁ v = tagVar Γ n₁ v
--
--tagExp Γ n (val a) = val (tagVal Γ n a)
--tagExp Γ n (case {u = u} {v = v} e e₁ e₂) = case (tagExp (tag 0 Γ) n e) 
--                                                 (tagExp (u ∷ tag 1 Γ) n e₁) 
--                                                 (tagExp (v ∷ tag 2 Γ) n e₂)
--tagExp Γ n (var v) = var (tagVar Γ n v)
--tagExp Γ n (fvar x) = {!fvar x!}
--tagExp Γ n (weak x e) = {!!}

sucExp' : ∀{n'}{Γ' : Cxt n'} → (u : Type) → 
       Γ' ⊆ (u ∷ Γ')
sucExp' u = weak u

replace : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
          Exp X (Γ ++ u ∷ Γ') t → Exp X Γ' u → Exp X (Γ ++ Γ') t
replace Γ e e' = {!e!}
--replace [] (weak e) e' = {!!}
--replace (x ∷ Γ) (weak e) e' = {!!}
--replace Γ (val x) e' = val (replaceV Γ x e')
--replace Γ (case {u}{v} e e₁ e₂) e' = case (replace Γ e e') 
--                                   (replace (u ∷ Γ) e₁ e') 
--                                   (replace (v ∷ Γ) e₂ e')
--replace Γ (var v) e' = {!!}
--replace Γ (fvar x) e' = {!!}


--replaceStruct [] (exchange u₁ u) e e' = {!!}
--replaceStruct [] (lift st) e e' = {!!}
--replaceStruct (x ∷ Γ) st e e' = {!!}


replaceV Γ unit e' = unit
replaceV Γ (inL e) e' = inL (replace Γ e e')
replaceV Γ (inR e) e' = inR (replace Γ e e')


--_⟨_⟩ : ∀{s u t}{X : VarSet}{Γ : Cxt s} → Exp X (u ∷ Γ) t → Exp X Γ u → Exp X Γ t
--_⟨_⟩ = {!!}
