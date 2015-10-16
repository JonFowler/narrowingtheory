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
  
--data Shape : Set where
--  zero : Shape 
--  var : Shape → Shape
--  tag : ℕ → Shape → Shape
 

  
Cxt : ℕ → Set
Cxt n = Vec Type n
--Cxt zero = Unit
--Cxt (var s) = Type × Cxt s
--Cxt (child x s) = Cxt s
  
--data Cxt : Shape → Set where
--  [] : Cxt zero
--  _∷_ : ∀{s} (t : Type) → Cxt s → Cxt (var s)
--  tag : ∀{s} → (n : ℕ) → Cxt s → Cxt (tag n s)

--_+ₛ_ : Shape → Shape → Shape
--zero +ₛ s2 = s2
--var s +ₛ s2 = var (s +ₛ s2)
--tag x s +ₛ s2 = tag x (s +ₛ s2)

--_++_ : ∀{s s'} → Cxt s → Cxt s' → Cxt (s +ₛ s')
--_++_ {zero} Γ Γ' = Γ'
--_++_ {var s} (t , Γ) Γ' = t , _++_ {s} Γ Γ'
--_++_ {child x s} Γ Γ' = _++_ {s} Γ Γ'

--infixr 5 _++_ 
--
--_++_ : ∀{s s'} → Cxt s → Cxt s' → Cxt (s +ₛ s')
--[] ++ Γ' = Γ'
--(t ∷ Γ) ++ Γ' = t ∷ (Γ ++ Γ')
--tag n Γ ++ Γ' = tag n (Γ ++ Γ')
--
--_⊆ₙ_ : ℕ → ℕ → Set
--s ⊆ₙ s' = ∃ (λ s'' → s'' +ₛ s' ≡ s)

--_⊆_ : ∀{n n'} → Cxt n → Cxt n' → Set
--_⊆_ {n}{n'} Γ Γ' = ∃₂ (λ (n'' : ℕ) (Γ'' : Cxt n'') → _≡_ {A = Σ ℕ (λ a → Cxt a)} (n'' + n' , Γ'' ++ Γ') (n , Γ))

--data _+1 (X : Set) : Set where
--  here : X +1
--  there : X → X +1
--  

VarSet : Set₁
VarSet = {n : ℕ} → Cxt n → Type → Set

Var : VarSet
Var [] t = ⊥
Var (t ∷ Γ) t₁ = t ≡ t₁ ⊎ Var Γ t₁

--lookup : {s : Shape} → Cxt s → Var s → Type
--lookup {zero} unit ()
--lookup {var s} (t , Γ) here = t
--lookup {var s} (t , Γ) (there x) = lookup {s} Γ x
--lookup {child x s} Γ v = lookup {s} Γ v

--lookup : {s : Shape} → Var s →  Cxt s → Type
--lookup () []
--lookup here (t ∷ Γ) = t
--lookup (there x) (t ∷ Γ)  = lookup x Γ  
--lookup v (tag n Γ) = lookup v Γ 
--
----shape-func : (s s' : Shape) → index s + index s' ≡ index (s +ₛ s')
----shape-func zero s' = refl
----shape-func (var s) s' = cong suc (shape-func s s')
----shape-func (child x s) s' = shape-func s s'
--
data Val {n : ℕ} (X : VarSet) (Γ : Cxt n)  : Type → Set₁

data _⊆_ : {n n' : ℕ} → (Γ' : Cxt n') → (Γ : Cxt n) → Set where
  weak : ∀{n}{Γ : Cxt n} → (u : Type) → Γ ⊆ (u ∷ Γ)
  exchange : ∀{n}{Γ : Cxt n} → (u t : Type) → (u ∷ t ∷ Γ) ⊆ (t ∷ u ∷ Γ)
  lift : ∀ {u n n'}{Γ : Cxt n}{Γ' : Cxt n'} → Γ ⊆ Γ'
                → (u ∷ Γ) ⊆ (u ∷ Γ')

data Exp {n : ℕ} (X : VarSet) (Γ : Cxt n)  (t : Type)  : Set₁ where
   val : (a : Val X Γ t) → Exp X Γ t
   case : ∀{u v} → Exp X Γ (u ⊕ v) → 
                    Exp X (u ∷ Γ) t → 
                    Exp X (v ∷ Γ) t → 
                    Exp X Γ t
                    
   var : (v : Var Γ t) → Exp X Γ t
   fvar : (x : X Γ t) → Exp X Γ t
   struct : ∀{n'}{Γ' : Cxt n'} → (Γ' ⊆ Γ) → Exp X Γ' t → Exp X Γ t
   
data Val {n : ℕ} (X : VarSet) (Γ : Cxt n)  where
   unit : Val X Γ V1
   inL : ∀{t u} (e : Exp X Γ t) → Val X Γ (t ⊕ u) 
   inR : ∀{t u} (e : Exp X Γ u) → Val X Γ (t ⊕ u) 

   
replaceV : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
        Val X (Γ ++ u ∷ Γ') t → Exp X (Γ ++ Γ') u → Val X (Γ ++ Γ') t
replaceV = {!!}


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

sucExp : ∀{u t n n'}{Γ' : Cxt n'}{X : VarSet} → (Γ : Cxt n) → 
       Exp X (Γ ++ Γ') t → Exp X (Γ ++ u ∷ Γ') t
sucExp Γ (val a) = {!!}
sucExp Γ (case e e₁ e₂) = {!!}
sucExp Γ (var v) = {!!}
sucExp Γ (fvar x) = {!!}
sucExp Γ (struct f e) = {!!}

sucExp' : ∀{n n'}{Γ' : Cxt n'} → (Γ : Cxt n) → (u : Type) → 
       (Γ ++ Γ') ⊆ (Γ ++ u ∷ Γ')
sucExp' [] u = weak u
sucExp' (x ∷ Γ) u = lift (sucExp' Γ u) 

replace : ∀{s s' u t}{X : VarSet}{Γ' : Cxt s'} → (Γ : Cxt s) → 
          Exp X (Γ ++ u ∷ Γ') t → Exp X (Γ ++ Γ') u → Exp X (Γ ++ Γ') t
replace Γ (val x) e' = val (replaceV Γ x e')
replace Γ (case {u}{v} e e₁ e₂) e' = case (replace Γ e e') 
                                   (replace (u ∷ Γ) e₁ {!e'!}) {!!}
replace Γ (var v) e' = {!!}
replace Γ (fvar x) e' = {!!}
replace Γ (struct a e) e' = {!!}


--_⟨_⟩ : ∀{s u t}{X : VarSet}{Γ : Cxt s} → Exp X (u ∷ Γ) t → Exp X Γ u → Exp X Γ t
--_⟨_⟩ = {!!}
