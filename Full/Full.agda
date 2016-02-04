module Full where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product

data B : Set where
  F : B
  T : B

  
data Expr (X : ℕ) : Set where
  bool : (b : B) → Expr X
  if : (e : Expr X) → (e' : Expr X) → (e'' : Expr X) → Expr X
  var : Fin X → Expr X

data Full (X : ℕ) : Set
data FullAlt (X : ℕ) : ℕ → Set where
  expr : Full X → FullAlt X 0
  alts : {n : ℕ} → FullAlt X n → FullAlt X n → FullAlt X n → FullAlt X (suc n)
  void : {n : ℕ} → FullAlt X n

data Full (X : ℕ) where
  bool : B → Full X
  var : Fin X → Full X
  match : {n : ℕ} → Vec (Full X) n → FullAlt X n → Full X

  
basic : {X : ℕ} → Expr X → Full X
basic (bool x) = bool x
basic (if e e' e'') = match [ basic e ] (alts void (expr (basic e')) (expr (basic e'')))
basic (var x) = var x


--evalExpr : {X : ℕ} → Expr X → (Vec B X) → B
--evalExpr (bool b) v = b
--evalExpr (if e e' e'') v with evalExpr e v 
--evalExpr (if e e' e'') v | F = evalExpr e' v
--evalExpr (if e e' e'') v | T = evalExpr e'' v
--evalExpr (var x) v = lookup x v 

data _⊑_ {X : Set} : Maybe X → Maybe X → Set where
  justjust : {x x₁ : X} → x ≡ x₁ → just x ⊑ just x₁ 
  noth : {b' : Maybe X} → nothing ⊑ b'

_⊑ₛ_ : {X : Set}{n : ℕ} → Vec (Maybe X) n → Vec (Maybe X) n → Set
[] ⊑ₛ [] = ⊤
(x ∷ v) ⊑ₛ (x₁ ∷ v') = (x ⊑ x₁) × (v ⊑ₛ v') 

Monotone : {X : Set}{n : ℕ} → (f : Vec (Maybe X) n → Maybe X) → Set
Monotone {X}{n} f = {v v' : Vec (Maybe X) n} → v ⊑ₛ v' → f v ⊑ f v' 


evalIf : {X : ℕ} → (Maybe B) → Expr X → Expr X → (Vec (Maybe B) X) → Maybe B
evalExpr : {X : ℕ} → Expr X → (Vec (Maybe B) X) → Maybe B

evalExpr (bool b) s = just b
evalExpr (if e e₁ e₂) s = evalIf (evalExpr e s) e₁ e₂ s
evalExpr (var x) s = lookup x s

evalIf (just F) e e' s = evalExpr e s
evalIf (just T) e e' s = evalExpr e' s
evalIf nothing e e' s = nothing


monotoneLookup : {X : ℕ}{A : Set} → (v : Fin X) → Monotone {X = A} (lookup v)
monotoneLookup zero {x ∷ _} {x₁ ∷ _} (o , _) = o
monotoneLookup (suc v) {_ ∷ s}{_ ∷ s'} (_ , os) = monotoneLookup v os

monotoneEvalIf : {X : ℕ}{b b' : Maybe B}(e e' : Expr X) → (b ⊑ b') → 
  {v v' : Vec (Maybe B) X} → v ⊑ₛ v' → evalIf b e e' v ⊑ evalIf b' e e' v' 

monotoneEvalExpr : {X : ℕ} → (e : Expr X) → Monotone (evalExpr e)
monotoneEvalExpr (bool b) o = justjust refl 
monotoneEvalExpr (if e e₁ e₂) o = monotoneEvalIf e₁ e₂ (monotoneEvalExpr e o) o
monotoneEvalExpr (var x) o = monotoneLookup x o

monotoneEvalIf {b = just F} e e' (justjust refl) os = monotoneEvalExpr e os
monotoneEvalIf {b = just T} e e' (justjust refl) os = monotoneEvalExpr e' os
monotoneEvalIf e e' noth os = noth


--evalFull : {X : ℕ} → 
