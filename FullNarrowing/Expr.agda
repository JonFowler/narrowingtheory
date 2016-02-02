module Expr where

open import Helpful
open import Subs

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

data Expr {V : ℕ} (Γ : Cxt V) (X : VarSet) : Ty → Set where
  Z : Expr Γ X Nat
  S : Expr Γ X Nat -> Expr Γ X Nat
  case_alt₀_altₛ_ : ∀{t} → (e : Expr Γ X Nat) → (e₀ : Expr Γ X t) 
                             → (eₛ : Expr (Nat ∷ Γ) X t) → Expr Γ X t
  var : ∀{t} → (v : Fin V) → (Γ [ v ]= t)  → Expr Γ X t
  fvar : (x : Var X) → Expr Γ X Nat
  
  app : ∀{u t} → Expr Γ X (u →ₜ t) → Expr Γ X u → Expr Γ X t
  lam : ∀{u t} → Expr (u ∷ Γ) X t → Expr Γ X (u →ₜ t)
  fix : ∀{t} → Expr Γ X (t →ₜ t) → Expr Γ X t
 
  

  
  
_⟪_⟫ : ∀{V X u t}{Γ : Cxt V} → Expr (u ∷ Γ) X t → Expr Γ X u → Expr Γ X t

-- the small step semantics for the language.
data _↦_ {V : ℕ}{Γ : Cxt V}{X : VarSet} {t : Ty} : Expr Γ X t → Expr Γ X t → Set where
  caseZ : ∀ e₀ eₛ → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : ∀ e e₀ eₛ → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : ∀{e e' e₀ eₛ} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               
-- New application rules
  subs : ∀{u} f → (e : Expr Γ X u) → app (lam f) e ↦ f ⟪ e ⟫
  promsub : ∀{u f f'}{e : Expr Γ X u}   → f ↦ f' → app f e ↦ app f' e
  
-- Rules for fix operator
  fix :  (f : Expr (t ∷ Γ) X t) → fix (lam f) ↦ f ⟪ fix (lam f) ⟫
  promfix : ∀{f f'} → f ↦ f' → fix f ↦ fix f' 

ValE : ∀{n X t}{Γ : Cxt n} → Expr Γ X t → Set
ValE Z = ⊤
ValE (S e) = ⊤
ValE (case e alt₀ e₁ altₛ e₂) = ⊥
ValE (var v x) = ⊥
ValE (fvar x) = ⊥
ValE (app e e₁) = ⊥
ValE (lam e) = ⊤
ValE (fix e) = ⊥

data _⇒_ {V : ℕ}{Γ : Cxt V}{X : VarSet} {t : Ty} : Expr Γ X t → Expr Γ X t → Set where

               
-- Transistive closure
data _↦*_ {V : ℕ}{Γ : Cxt V}{X : VarSet}{t : Ty} : Expr Γ X t → Expr Γ X t → Set where
  [] : ∀{e} → e ↦* e 
  _∷_ : ∀{e e' e''} → (r : e ↦ e') → (r* : e' ↦* e'') → e ↦* e''
  
-- Embedding of values into expressions.
⌈_⌉ : ∀{V X}{Γ : Cxt V} → Val X → Expr Γ X Nat
⌈ fvar x ⌉ = fvar x
⌈ Z ⌉ = Z
⌈ S a ⌉ = S ⌈ a ⌉
  
-- The application of a free variable substitution, σ : X ⇀ Y , to a expression
_⟦_⟧ : ∀{V X Y t}{Γ : Cxt V} →  (e : Expr Γ X t) → X ⇀ Y → Expr Γ Y t
Z ⟦ σ ⟧ = Z
S e ⟦ σ ⟧ = S (e ⟦ σ ⟧)
var x o ⟦ σ ⟧ = var x o
fvar x ⟦ σ ⟧ = ⌈ σ x ⌉
(case e alt₀ e₀ altₛ eₛ) ⟦ σ ⟧ = case e ⟦ σ ⟧ alt₀ e₀ ⟦ σ ⟧ altₛ eₛ ⟦ σ ⟧ 
app f e ⟦ σ ⟧ = app (f ⟦ σ ⟧) (e ⟦ σ ⟧)
lam f ⟦ σ ⟧ = lam (f ⟦ σ ⟧)
fix f ⟦ σ ⟧ = fix (f ⟦ σ ⟧)


-- The definiton of de bruijn substitution follows
sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucCxt : ∀{V V' u t}{Γ' : Cxt V'}(Γ : Cxt V) → (v : Fin (V + V')) → 
         Γ ++ Γ' [ v ]= t → Γ ++ u ∷ Γ' [ sucVar V v ]= t
sucCxt [] v o = there o
sucCxt (t ∷ Γ) zero here = here
sucCxt (x ∷ Γ) (suc v) (there o) = there (sucCxt Γ v o)

sucExpr : ∀{V V' t u X}{Γ' : Cxt V'} → (Γ : Cxt V) → Expr (Γ ++ Γ') X t → Expr (Γ ++ u ∷ Γ') X t
sucExpr Γ Z = Z
sucExpr Γ (S x) = S (sucExpr Γ x)
sucExpr {V = V} Γ (var x o) = var (sucVar V x) (sucCxt Γ x o)
sucExpr Γ (fvar x) = fvar x
sucExpr Γ (case e alt₀ e₁ altₛ e₂) = 
       case (sucExpr Γ e) alt₀ (sucExpr Γ e₁) altₛ sucExpr (Nat ∷ Γ) e₂
sucExpr Γ (app f e) = app (sucExpr Γ f) (sucExpr Γ e)
sucExpr Γ (lam {u = u} f) = lam (sucExpr (u ∷ Γ) f)
sucExpr Γ (fix f) = fix (sucExpr Γ f)

rep : ∀{V V' t u X}{Γ' : Cxt V'}(Γ : Cxt V) → Expr (Γ ++ u ∷ Γ') X t → Expr Γ' X u → Expr (Γ ++ Γ') X t
rep Γ Z ef = Z
rep Γ (S x) ef = S (rep Γ x ef)
rep [] (var zero here) ef = ef 
rep [] (var (suc v) (there o)) ef = var v o
rep (x ∷ Γ) (var zero here) ef = var zero here
rep (x ∷ Γ) (var (suc v) (there o)) ef = sucExpr [] (rep Γ (var v o) ef )
rep Γ (fvar a) ef = fvar a
rep Γ (case e alt₀ e₁ altₛ e₂) ef = case rep Γ e ef alt₀ rep Γ e₁ ef altₛ rep (Nat ∷ Γ) e₂ ef
rep Γ (app {u = u} f e) ef = app (rep Γ f ef) (rep Γ e ef)
rep Γ (lam {u = u} f) ef = lam (rep (u ∷ Γ) f ef)
rep Γ (fix f) ef = fix (rep Γ f ef)

_⟪_⟫ = rep [] 
