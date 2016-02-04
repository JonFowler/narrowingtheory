module Full where

open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (_+_) 
open import Data.Vec hiding (_>>=_) 
open import Data.Maybe
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Relation.Nullary

data B : Set where
  F : B
  T : B

  
data Expr (X : ℕ) : Set where
  bool : (b : B) → Expr X
  if : (e : Expr X) → (e' : Expr X) → (e'' : Expr X) → Expr X
  var : (v : Fin X) → Expr X

Inp : ℕ → Set
Inp n = Vec (Maybe B) n

Out : Set
Out = Maybe B

data Full (X : ℕ) : Set
data FullAlt (X : ℕ) : ℕ → Set where
  expr : (e : Full X) → FullAlt X 0
  alts : {n : ℕ} → Maybe (FullAlt X n) → Maybe (FullAlt X n) → Maybe (FullAlt X n) → FullAlt X (suc n)

data Full (X : ℕ) where
  bool : (b : B) → Full X
  var : (v : Fin X) → Full X
  match : (Full X) → Maybe (Full X) → Maybe (Full X) → Maybe (Full X) → Full X

  
basic : {X : ℕ} → Expr X → Full X
basic (bool x) = bool x
basic (if e e' e'') = match (basic e) nothing (just (basic e')) (just (basic e''))
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

evalIf : {X : ℕ} → (Maybe B) → Expr X → Expr X → Inp X → Out
evalExpr : {X : ℕ} → Expr X → Inp X → Out

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


evalMatch : ∀{X} → Maybe B → Maybe (Full X) → Maybe (Full X) → Maybe (Full X) → Inp X → Maybe B
evalFull : {X : ℕ} → Full X → Inp X → Maybe B

evalFull (bool b) s = just b
evalFull (var v) s = lookup v s
evalFull (match e n ef et) s = evalMatch (evalFull e s) n ef et s

evalMatch nothing (just e) ef et s = evalFull e s
evalMatch nothing nothing ef et s = nothing
evalMatch (just F) _ (just e) _ s = evalFull e s
evalMatch (just F) _ nothing _ s = nothing
evalMatch (just T) _ _ (just e) s = evalFull e s
evalMatch (just T) _ _ nothing s = nothing


basicEquiv : ∀{X} → (e : Expr X) → (s : Inp X) → evalExpr e s ≡ evalFull (basic e) s
basicMatchEquiv : ∀{X} → (b : Maybe B) → (e e' : Expr X) → (s : Inp X) 
    → evalIf b e e' s ≡ evalMatch b nothing (just (basic e)) (just (basic e')) s

basicMatchEquiv (just F) e e' s = basicEquiv e s
basicMatchEquiv (just T) e e' s = basicEquiv e' s
basicMatchEquiv nothing e e' s = refl

basicEquiv (bool b) s = refl
basicEquiv (if e e₁ e₂) s = trans (cong (λ x → evalIf x e₁ e₂ s) (basicEquiv e s)) 
                                  (basicMatchEquiv (evalFull (basic e) s) e₁ e₂ s) 
basicEquiv (var v) s = refl

maybeMatch : ∀{X} → Full X → Maybe (Full X) → Maybe (Full X) → Maybe (Full X) → Maybe (Full X)
maybeMatch e nothing nothing nothing = nothing
maybeMatch e (just e') nothing nothing = just e' 
maybeMatch e f f' f'' = just (match e f f' f'')

sucEq : ∀{N}{m n : Fin N} → _≡_ {A = Fin (suc N)} (suc m) (suc n) → m ≡ n 
sucEq refl = refl

_≟_ : {N : ℕ} → (m : Fin N) → (n : Fin N) → Dec (m ≡ n) --Dec (m ≡ n)
zero ≟ zero = yes refl
zero ≟ suc n₁ = no (λ ())
suc m ≟ zero = no (λ ())
suc m ≟ suc n with m ≟ n
suc m ≟ suc n₁ | yes p = yes (cong suc p)
suc m ≟ suc n₁ | no ¬p = no (λ x → ¬p (sucEq x))

unifyBool : ∀{X} → B → B → Maybe (Full X)
unifyBool F F = just (bool F)
unifyBool F T = nothing
unifyBool T F = nothing
unifyBool T T = just (bool T)

unifyVarBool : ∀{X} → (v : Fin X) → B → Maybe (Full X)
unifyVarBool v F = just (match (var v) nothing (just (bool F)) nothing)
unifyVarBool v T = just (match (var v) nothing nothing (just (bool T)))

unify : ∀{X} → Full X → Full X → Maybe (Full X)
unifyMaybe : ∀{X} → Full X → Maybe (Full X) → Maybe (Full X)
unifyMaybeMaybe : ∀{X} → Maybe (Full X) → Maybe (Full X) → Maybe (Full X)
unifyVarMatch : ∀{X} → (v : Fin X) → Full X → (e e' e'' : Maybe (Full X)) → Maybe (Full X)
unifyMatchSym : ∀{X} → Full X → Full X → (f f' f'' : Maybe (Full X)) → Maybe (Full X)
--unifyMatchs : ∀{X} → Full X → (f f' f'' : Maybe (Full X)) → 
--                      Full X → (g g' g'' : Maybe (Full X)) → Maybe (Full X)

unifyMaybe e (just x) = unify e x
unifyMaybe e nothing = nothing

unifyMaybeMaybe nothing e = nothing
unifyMaybeMaybe (just e) f = unifyMaybe e f

unifyVarMatch v (var v') f f' f'' with v ≟ v'
unifyVarMatch v (var .v) f f' f'' | yes refl = maybeMatch (var v) 
                                                  (unifyMaybe (var v) f) 
                                                  (unifyMaybe (bool F) f') 
                                                  (unifyMaybe (bool T) f'')
unifyVarMatch v (var v') f f' f'' | no ¬p = unifyMatchSym (var v) (var v') f f' f'' 
unifyVarMatch v e f f' f'' = unifyMatchSym (var v) e f f' f'' 
                                          
unifyMatchSym u e f f' f'' = maybeMatch e (unifyMaybe u f ) 
                                          (unifyMaybe u f') 
                                          (unifyMaybe u f'')

--unifyMatchs (var v) f f' f'' (var v') g g' g'' with v ≟ v'
--unifyMatchs (var v) f f' f'' (var .v) g g' g'' | yes refl = just (match (var v) 
--           (unifyMaybeMaybe f g) 
--           (unifyMaybeMaybe f' g') 
--           (unifyMaybeMaybe f'' g''))
--unifyMatchs (var v) f f' f'' (var v') g g' g'' | no ¬p = maybeMatch (var v') 
--  (unifyMaybe (match (var v) f f' f'') g)
--  ?
--  ?
--unifyMatchs e f f' f'' e' g g' g'' = {!!}

unify (bool b) (bool b') = unifyBool b b'
unify (bool b) (var v) = unifyVarBool v b 
unify (bool b) (match e f f' f'') = unifyMatchSym (bool b) e f f' f'' 
unify (var v) (bool b) = unifyVarBool v b
unify (var v) (var v₁) with v ≟ v₁
unify (var v) (var .v) | yes refl = just (var v)
unify (var v) (var v₁) | no ¬p = just (match (var v) nothing (just vF) (just vT))
  where vF = match (var v₁) nothing (just (bool F)) nothing
        vT = match (var v₁) nothing nothing (just (bool T))
unify (var v) (match e' x x₁ x₂) = unifyVarMatch v e' x x₁ x₂
unify (match e f f' f'') (bool b) = unifyMatchSym (bool b) e f f' f''
unify (match e f f' f'') (var v) = unifyVarMatch v e f f' f'' 
unify (match (var v) f f' f'') (match (var v') g g' g'') with v ≟ v'
unify (match (var v) f f' f'') (match (var .v) g g' g'') | yes refl = just (match (var v) 
           (unifyMaybeMaybe f g) 
           (unifyMaybeMaybe f' g') 
           (unifyMaybeMaybe f'' g''))
unify (match (var v) f f' f'') (match (var v') g g' g'') | no ¬p = maybeMatch (var v') 
  (unifyMaybe (match (var v) f f' f'') g) 
  (unifyMaybe (match (var v) f f' f'') g') 
  (unifyMaybe (match (var v) f f' f'') g'') 
unify (match e f f' f'') (match e' g g' g'') = maybeMatch e' 
  (unifyMaybe (match e f f' f'') g) 
  (unifyMaybe (match e f f' f'') g')
  (unifyMaybe (match e f f' f'') g'')

full : {X : ℕ} → Expr X → Full X
full (bool b) = bool b
full (if e e' e'') = match (full e) (unify f' f'') (just f') (just f'') -- match {!!} {!!}
  where f' = full e'
        f'' = full e''
full (var v) = var v


