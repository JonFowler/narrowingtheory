module STLC where

open import Helpful
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

--data Val {n : ℕ} (X : VarSet) (Γ : Cxt n)  : Type → Set

--data _⊆_ : {n n' : ℕ} → (Γ' : Cxt n') → (Γ : Cxt n) → Set where
--  weak : ∀{n}{Γ : Cxt n} → (u : Type) → Γ ⊆ (u ∷ Γ)
--  exchange : ∀{n}{Γ : Cxt n} → (u t : Type) → (u ∷ t ∷ Γ) ⊆ (t ∷ u ∷ Γ)
--  lift : ∀ {u n n'}{Γ : Cxt n}{Γ' : Cxt n'} → Γ ⊆ Γ'
              --→ (u ∷ Γ) ⊆ (u ∷ Γ')
              
data Subst (X : VarSet) : {n n' : ℕ} → (Γ : Cxt n) → (Γ' : Cxt n') → Set 
              
data Exp (X : VarSet) {n : ℕ} (Γ : Cxt n) : (t : Type) → Set where

   unit : Exp X Γ V1
   inL : ∀{t u} (e : Exp X Γ t) → Exp X Γ (t ⊕ u) 
   inR : ∀{t u} (e : Exp X Γ u) → Exp X Γ (t ⊕ u) 

--   val : (a :  X Γ t) → Exp X Γ t
   case : ∀{u v t} → Exp X Γ (u ⊕ v) → 
                    Exp X (u ∷ Γ) t → 
                    Exp X (v ∷ Γ) t → 
                    Exp X Γ t
   var : ∀{t}(v : Var Γ t) → Exp X Γ t
   fvar : ∀{n' t}{Γ' : Cxt n'}(x : X Γ' t) → 
             Subst X Γ' Γ → Exp X Γ t
                     
                           
data Subst (X : VarSet) where
  [] : ∀{n}{Γ : Cxt n} → Subst X Γ Γ
  sucE : ∀{u n n' n''} → {Γ' : Cxt n'}{Γ'' : Cxt n''} → (Γ : Cxt n) →  
               Subst X Γ'' (Γ ++ Γ') → Subst X Γ'' (Γ ++ u ∷ Γ')
  repl : ∀{n n' n'' u}{Γ' : Cxt n'}{Γ'' : Cxt n''} → (Γ : Cxt n) → (e : Exp X Γ' u) → 
                Subst X Γ'' (Γ ++ u ∷ Γ') → Subst X Γ'' (Γ ++ Γ') 

   
--data Val {n : ℕ} (X : VarSet) (Γ : Cxt n)  where
   
--replaceV : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
--        Val X (Γ ++ u ∷ Γ') t → Exp X Γ' u → Val X (Γ ++ Γ') t

sucVar : ∀{n n' u t}{Γ' : Cxt n'} → (Γ : Cxt n) → Var (Γ ++ Γ') t → Var (Γ ++ u ∷ Γ') t
sucVar [] v = inj₂ v
sucVar (x ∷ Γ) (inj₁ eq) = inj₁ eq
sucVar (x ∷ Γ) (inj₂ y) = inj₂ (sucVar Γ y)

sucExp : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
          Exp X (Γ ++ Γ') t → Exp X (Γ ++ u ∷ Γ') t

--sucVal : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
--          Val X (Γ ++ Γ') t → Val X (Γ ++ u ∷ Γ') t

--sucVal Γ unit = unit
--sucVal Γ (inL e) = inL (sucExp Γ e)
--sucVal Γ (inR e) = inR (sucExp Γ e)

sucExp Γ (unit) = unit
sucExp Γ (inL a) =  inL (sucExp Γ a)
sucExp Γ (inR a) = inR (sucExp Γ a)
sucExp Γ (case {u}{v} e e₁ e₂) = case (sucExp Γ e) (sucExp (u ∷ Γ) e₁) (sucExp (v ∷ Γ) e₂)
sucExp Γ (var v) = var (sucVar Γ v) 
sucExp Γ (fvar x sub) = fvar x (sucE Γ sub)


replace : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
          Exp X (Γ ++ u ∷ Γ') t → Exp X Γ' u → Exp X (Γ ++ Γ') t
replace Γ unit e' = unit 
replace Γ (inL e) e' =  inL (replace Γ e e') 
replace Γ (inR e) e' = inR (replace Γ e e') 
replace Γ (case {u}{v} e e₁ e₂) e' = case (replace Γ e e') 
                                   (replace (u ∷ Γ) e₁ e') 
                                   (replace (v ∷ Γ) e₂ e')
replace [] (var (inj₁ refl)) e' = e'
replace [] (var (inj₂ y)) e' = var y
replace (t ∷ Γ) (var (inj₁ eq)) e' = var (inj₁ eq)
replace (x ∷ Γ) (var (inj₂ v)) e'  = sucExp [] (replace Γ (var v) e')
replace Γ (fvar x s) e' = fvar x (repl Γ e' s) 

--_>>=val_ : ∀{n t}{X Y : VarSet}{Γ : Cxt n} → Val X Γ t → 
--             (∀{m u}{Δ : Cxt m} → X Δ u → Exp Y Δ u) → Val Y Γ t

_⇀ₛ_ : VarSet → VarSet → Set
X ⇀ₛ Y = (∀{m u}{Δ : Cxt m} → X Δ u → Exp Y Δ u)

_>>=ₛ_ : ∀{n t}{X Y : VarSet}{Γ : Cxt n} → Exp X Γ t → 
             X ⇀ₛ Y → Exp Y Γ t
unit >>=ₛ σ = unit
inL e >>=ₛ σ = inL (e >>=ₛ σ)
inR e >>=ₛ σ = inR (e >>=ₛ σ)
case e e₁ e₂ >>=ₛ σ = case (e >>=ₛ σ) (e₁ >>=ₛ σ) (e₂ >>=ₛ σ)
var v >>=ₛ σ = var v
fvar x [] >>=ₛ σ = σ x
fvar x (sucE Γ s) >>=ₛ σ = sucExp Γ (fvar x s >>=ₛ σ)
fvar x (repl Γ e s) >>=ₛ σ = replace Γ (fvar x s >>=ₛ σ) (e >>=ₛ σ)

lift-sucExp : ∀{s s' u t}{X Y : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → (σ : X ⇀ₛ Y) → 
          (e : Exp X (Γ ++ Γ') t) → (sucExp {u = u} Γ e >>=ₛ σ) ≡ sucExp Γ (e >>=ₛ σ)
lift-sucExp Γ σ e = {!!}



lift-replace : ∀{n n' t u}{Γ' : Cxt n'}{X Y : VarSet}(Γ : Cxt n) → (σ : X ⇀ₛ Y) → 
                 (e : Exp X (Γ ++ u ∷ Γ') t) → (e' : Exp X Γ' u) →
               (replace Γ e e' >>=ₛ σ) ≡ replace Γ (e >>=ₛ σ) (e' >>=ₛ σ)
lift-replace Γ σ unit e' = refl
lift-replace Γ σ (inL e) e' = cong inL (lift-replace Γ σ e e')
lift-replace Γ σ (inR e) e' = cong inR (lift-replace Γ σ e e')
lift-replace Γ σ (case {u}{v} e e₁ e₂) e' = cong₃ case (lift-replace Γ σ e e') 
                                                       (lift-replace (u ∷ Γ) σ e₁ e') 
                                                       (lift-replace (v ∷ Γ) σ e₂ e') 
lift-replace [] σ (var (inj₁ refl)) e' = refl
lift-replace [] σ (var (inj₂ v)) e' = refl
lift-replace (x ∷ Γ) σ (var (inj₁ eq)) e' = refl
lift-replace (x ∷ Γ) σ (var (inj₂ v)) e' = let v = lift-replace Γ σ (var v) e' 
             in {!!} -- lift-sucExp [] σ {!!} 
lift-replace Γ σ (fvar x x₁) e' = {!!}



-- (subs {!Γ!} {!!} {!s!}) -- fvar {!!} x (subs {!Γ!} {!!} {!s!}) -- fvar x {!!}
--replace [] (weak e) e' = {!!}
--replace (x ∷ Γ) (weak e) e' = {!!}

--replaceStruct [] (exchange u₁ u) e e' = {!!}
--replaceStruct [] (lift st) e e' = {!!}
--replaceStruct (x ∷ Γ) st e e' = {!!}


--replaceV Γ unit e' = unit
--replaceV Γ (inL e) e' = inL (replace Γ e e')
--replaceV Γ (inR e) e' = inR (replace Γ e e')


--_⟨_⟩ : ∀{s u t}{X : VarSet}{Γ : Cxt s} → Exp X (u ∷ Γ) t → Exp X Γ u → Exp X Γ t
--_⟨_⟩ = {!!}
