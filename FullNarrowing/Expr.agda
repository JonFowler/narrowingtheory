module Expr where

open import Helpful
open import Subs

open import Coinduction

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Unit
open import Data.Empty
open import Data.List hiding (_++_)

data Ty : Set where
  Nat : Ty
  _→ₜ_ : Ty → Ty → Ty

Cxt : ℕ → Set
Cxt = Vec Ty



data Term {V : ℕ} (Γ : Cxt V) (X : VarSet) : Ty → Set where
  Z : Term Γ X Nat
  S : ∞ (Term Γ X Nat) -> Term Γ X Nat
  case_alt₀_altₛ_ : ∀{t} → (e : Term Γ X Nat) → (e₀ : Term Γ X t) 
                             → (eₛ : Term (Nat ∷ Γ) X t) → Term Γ X t

data NF {V : ℕ} (Γ : Cxt V) (X : VarSet) : Ty → Set where
  Z : NF Γ X Nat
  S : ∞ (NF Γ X Nat) ->  NF Γ X Nat

--  var : ∀{t} → (v : Fin V) → (Γ [ v ]= t)  → Term Γ X t
--  fvar : (x : Var X) → Term Γ X Nat
--  
--  app : ∀{u t} → Term Γ X (u →ₜ t) → Term Γ X u → Term Γ X t
--  lam : ∀{u t} → Term (u ∷ Γ) X t → Term Γ X (u →ₜ t)
--  fix : ∀{t} → Term Γ X (t →ₜ t) → Term Γ X t
 
  

  
  
_⟪_⟫ : ∀{V X u t}{Γ : Cxt V} → Term (u ∷ Γ) X t → Term Γ X u → Term Γ X t
_⟪_⟫ = {!!}

-- the small step semantics for the language.
data _↦_ {V : ℕ}{Γ : Cxt V}{X : VarSet} {t : Ty} : Term Γ X t → Term Γ X t → Set where
  caseZ : ∀ e₀ eₛ → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : ∀ e e₀ eₛ → case (S (♯ e)) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : ∀{e e' e₀ eₛ} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               
data _↦!_ {V : ℕ}{Γ : Cxt V}{X : VarSet} {t : Ty} : Term Γ X t → Term Γ X t → Set where


               
---- New application rules
--  subs : ∀{u} f → (e : Term Γ X u) → app (lam f) e ↦ f ⟪ e ⟫
--  promsub : ∀{u f f'}{e : Term Γ X u}   → f ↦ f' → app f e ↦ app f' e
--  
---- Rules for fix operator
--  fix :  (f : Term (t ∷ Γ) X t) → fix (lam f) ↦ f ⟪ fix (lam f) ⟫
--  promfix : ∀{f f'} → f ↦ f' → fix f ↦ fix f' 

--ValE : ∀{n X t}{Γ : Cxt n} → Term Γ X t → Set
--ValE Z = ⊤
--ValE (S e) = ⊤
--ValE (case e alt₀ e₁ altₛ e₂) = ⊥
----ValE (var v x) = ⊥
----ValE (fvar x) = ⊥
----ValE (app e e₁) = ⊥
----ValE (lam e) = ⊤
----ValE (fix e) = ⊥
--
--data _⇒_ {V : ℕ}{Γ : Cxt V}{X : VarSet} {t : Ty} : Term Γ X t → Term Γ X t → Set where
--
--               
---- Transistive closure
--data _↦*_ {V : ℕ}{Γ : Cxt V}{X : VarSet}{t : Ty} : Term Γ X t → Term Γ X t → Set where
--  [] : ∀{e} → e ↦* e 
--  _∷_ : ∀{e e' e''} → (r : e ↦ e') → (r* : e' ↦* e'') → e ↦* e''
--  
---- Embedding of values into expressions.
--⌈_⌉ : ∀{V X}{Γ : Cxt V} → Val X → Term Γ X Nat
--⌈ fvar x ⌉ = fvar x
--⌈ Z ⌉ = Z
--⌈ S a ⌉ = S ⌈ a ⌉
--  
---- The application of a free variable substitution, σ : X ⇀ Y , to a expression
--_⟦_⟧ : ∀{V X Y t}{Γ : Cxt V} →  (e : Term Γ X t) → X ⇀ Y → Term Γ Y t
--Z ⟦ σ ⟧ = Z
--S e ⟦ σ ⟧ = S (e ⟦ σ ⟧)
--var x o ⟦ σ ⟧ = var x o
--fvar x ⟦ σ ⟧ = ⌈ σ x ⌉
--(case e alt₀ e₀ altₛ eₛ) ⟦ σ ⟧ = case e ⟦ σ ⟧ alt₀ e₀ ⟦ σ ⟧ altₛ eₛ ⟦ σ ⟧ 
--app f e ⟦ σ ⟧ = app (f ⟦ σ ⟧) (e ⟦ σ ⟧)
--lam f ⟦ σ ⟧ = lam (f ⟦ σ ⟧)
--fix f ⟦ σ ⟧ = fix (f ⟦ σ ⟧)
--
--
---- The definiton of de bruijn substitution follows
--sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
--sucVar zero n = suc n
--sucVar (suc V) zero = zero
--sucVar (suc V) (suc n) = suc (sucVar V n)
--
--sucCxt : ∀{V V' u t}{Γ' : Cxt V'}(Γ : Cxt V) → (v : Fin (V + V')) → 
--         Γ ++ Γ' [ v ]= t → Γ ++ u ∷ Γ' [ sucVar V v ]= t
--sucCxt [] v o = there o
--sucCxt (t ∷ Γ) zero here = here
--sucCxt (x ∷ Γ) (suc v) (there o) = there (sucCxt Γ v o)
--
--sucTerm : ∀{V V' t u X}{Γ' : Cxt V'} → (Γ : Cxt V) → Term (Γ ++ Γ') X t → Term (Γ ++ u ∷ Γ') X t

--sucTerm Γ (S x) = S (sucTerm Γ x)
--sucTerm {V = V} Γ (var x o) = var (sucVar V x) (sucCxt Γ x o)
--sucTerm Γ (fvar x) = fvar x
--sucTerm Γ (case e alt₀ e₁ altₛ e₂) = 
--       case (sucTerm Γ e) alt₀ (sucTerm Γ e₁) altₛ sucTerm (Nat ∷ Γ) e₂
--sucTerm Γ (app f e) = app (sucTerm Γ f) (sucTerm Γ e)
--sucTerm Γ (lam {u = u} f) = lam (sucTerm (u ∷ Γ) f)
--sucTerm Γ (fix f) = fix (sucTerm Γ f)
--
--rep : ∀{V V' t u X}{Γ' : Cxt V'}(Γ : Cxt V) → Term (Γ ++ u ∷ Γ') X t → Term Γ' X u → Term (Γ ++ Γ') X t
--rep Γ Z ef = Z
--rep Γ (S x) ef = S (rep Γ x ef)
--rep [] (var zero here) ef = ef 
--rep [] (var (suc v) (there o)) ef = var v o
--rep (x ∷ Γ) (var zero here) ef = var zero here
--rep (x ∷ Γ) (var (suc v) (there o)) ef = sucTerm [] (rep Γ (var v o) ef )
--rep Γ (fvar a) ef = fvar a
--rep Γ (case e alt₀ e₁ altₛ e₂) ef = case rep Γ e ef alt₀ rep Γ e₁ ef altₛ rep (Nat ∷ Γ) e₂ ef
--rep Γ (app {u = u} f e) ef = app (rep Γ f ef) (rep Γ e ef)
--rep Γ (lam {u = u} f) ef = lam (rep (u ∷ Γ) f ef)
--rep Γ (fix f) ef = fix (rep Γ f ef)
--
--_⟪_⟫ = rep [] 
