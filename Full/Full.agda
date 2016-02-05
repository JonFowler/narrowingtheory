module Full where

open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (_+_) 
open import Data.Vec hiding (_>>=_) 
--open import Data.Maybe
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Relation.Nullary

data B : Set where
  T : B
  F : B
  bot : B

  
data Expr (X : ℕ) : Set where
  val : B → Expr X
  if : (e : Expr X) → (e' : Expr X) → (e'' : Expr X) → Expr X
  var : (v : Fin X) → Expr X

Inp : ℕ → Set
Inp n = Vec B n

data Full (X : ℕ) : Set where
  val : B → Full X
  var : (v : Fin X) → Full X
  match : (Full X) → Full X → Full X → Full X → Full X

  
basic : {X : ℕ} → Expr X → Full X
basic (val x) = val x
basic (if e e' e'') = match (basic e) (val bot) (basic e') (basic e'')
basic (var x) = var x

--evalExpr : {X : ℕ} → Expr X → (Vec B X) → B
--evalExpr (val b) v = b
--evalExpr (if e e' e'') v with evalExpr e v 
--evalExpr (if e e' e'') v | F = evalExpr e' v
--evalExpr (if e e' e'') v | T = evalExpr e'' v
--evalExpr (var x) v = lookup x v 

data _⊑_ : B → B → Set where
  TT : T ⊑ T
  FF : F ⊑ F
  bot : {b : B} → bot ⊑ b

refl-⊑ : ∀{b} → b ⊑ b
refl-⊑ {T} = TT
refl-⊑ {F} = FF
refl-⊑ {bot} = bot

_⊑ₛ_ : {n : ℕ} → Vec B n → Vec B n → Set
[] ⊑ₛ [] = ⊤
(x ∷ v) ⊑ₛ (x₁ ∷ v') = (x ⊑ x₁) × (v ⊑ₛ v') 

Monotone : {n : ℕ} → (f : Vec B n → B) → Set
Monotone {n} f = {v v' : Vec B n} → v ⊑ₛ v' → f v ⊑ f v' 

evalIf : {X : ℕ} → B → Expr X → Expr X → Inp X → B 
evalExpr : {X : ℕ} → Expr X → Inp X → B 

evalExpr (val b) s = b
evalExpr (if e e₁ e₂) s = evalIf (evalExpr e s) e₁ e₂ s
evalExpr (var x) s = lookup x s

evalIf T e e' s = evalExpr e s
evalIf F e e' s = evalExpr e' s
evalIf ⊥ e e' s = ⊥ 

monotoneLookup : {X : ℕ} → (v : Fin X) → Monotone (lookup v)
monotoneLookup zero {x ∷ _} {x₁ ∷ _} (o , _) = o
monotoneLookup (suc v) {_ ∷ s}{_ ∷ s'} (_ , os) = monotoneLookup v os

monotoneEvalIf : {X : ℕ}{b b' : B}(e e' : Expr X) → (b ⊑ b') → 
  {v v' : Vec B X} → v ⊑ₛ v' → evalIf b e e' v ⊑ evalIf b' e e' v' 

monotoneEvalExpr : {X : ℕ} → (e : Expr X) → Monotone (evalExpr e)
monotoneEvalExpr (val b) o = refl-⊑ 
monotoneEvalExpr (if e e₁ e₂) o = monotoneEvalIf e₁ e₂ (monotoneEvalExpr e o) o
monotoneEvalExpr (var x) o = monotoneLookup x o

monotoneEvalIf {b = T} e e' TT os = monotoneEvalExpr e os
monotoneEvalIf {b = F} e e' FF os = monotoneEvalExpr e' os
monotoneEvalIf {b = bot} e e' bot os = bot

evalMatch : ∀{X} → B → Full X → Full X → Full X → Inp X → B
evalFull : {X : ℕ} → Full X → Inp X → B

evalFull (val b) s = b
evalFull (var v) s = lookup v s
evalFull (match e n et ef) s = evalMatch (evalFull e s) n et ef s

evalMatch T n et ef s = evalFull et s
evalMatch F n et ef s = evalFull ef s
evalMatch bot n et ef s = evalFull n s

basicEquiv : ∀{X} → (e : Expr X) → (s : Inp X) → evalExpr e s ≡ evalFull (basic e) s
basicMatchEquiv : ∀{X} → (b : B) → (e e' : Expr X) → (s : Inp X) 
    → evalIf b e e' s ≡ evalMatch b (val bot) (basic e) (basic e') s

basicMatchEquiv T e e' s = basicEquiv e s
basicMatchEquiv F e e' s = basicEquiv e' s
basicMatchEquiv bot e e' s = refl

basicEquiv (val b) s = refl
basicEquiv (if e e₁ e₂) s = trans (cong (λ x → evalIf x e₁ e₂ s) (basicEquiv e s)) 
                                  (basicMatchEquiv (evalFull (basic e) s) e₁ e₂ s) 
basicEquiv (var v) s = refl

maybeMatch : ∀{X} → Full X → Full X → Full X → Full X → Full X
maybeMatch e (val bot) (val bot) (val bot) = val bot
maybeMatch e e' (val bot) (val bot) = e' 
maybeMatch e f f' f'' = match e f f' f''

sucEq : ∀{N}{m n : Fin N} → _≡_ {A = Fin (suc N)} (suc m) (suc n) → m ≡ n 
sucEq refl = refl

_≟_ : {N : ℕ} → (m : Fin N) → (n : Fin N) → Dec (m ≡ n) --Dec (m ≡ n)
zero ≟ zero = yes refl
zero ≟ suc n₁ = no (λ ())
suc m ≟ zero = no (λ ())
suc m ≟ suc n with m ≟ n
suc m ≟ suc n₁ | yes p = yes (cong suc p)
suc m ≟ suc n₁ | no ¬p = no (λ x → ¬p (sucEq x))

unifyBool : ∀{X} → B → B → Full X
unifyBool T T = val T
unifyBool T F = val bot
unifyBool T bot = val bot
unifyBool F T = val bot 
unifyBool F F = val F
unifyBool F bot = val bot
unifyBool bot e' = val bot 

--unifyVarBool : ∀{X} → (v : Fin X) → B → Maybe (Full X)
--unifyVarBool v F = just (match (var v) nothing (just (bool F)) nothing)
--unifyVarBool v T = just (match (var v) nothing nothing (just (bool T)))
--
--unify : ∀{X} → Full X → Full X → Maybe (Full X)
--unifyMaybe : ∀{X} → Full X → Maybe (Full X) → Maybe (Full X)
--unifyMaybeMaybe : ∀{X} → Maybe (Full X) → Maybe (Full X) → Maybe (Full X)
--unifyVarMatch : ∀{X} → (v : Fin X) → Full X → (e e' e'' : Maybe (Full X)) → Maybe (Full X)
--unifyMatchSym : ∀{X} → Full X → Full X → (f f' f'' : Maybe (Full X)) → Maybe (Full X)
----unifyMatchs : ∀{X} → Full X → (f f' f'' : Maybe (Full X)) → 
----                      Full X → (g g' g'' : Maybe (Full X)) → Maybe (Full X)
--
--unifyMaybe e (just x) = unify e x
--unifyMaybe e nothing = nothing
--
--unifyMaybeMaybe nothing e = nothing
--unifyMaybeMaybe (just e) f = unifyMaybe e f
--
--unifyVarMatch v (var v') f f' f'' with v ≟ v'
--unifyVarMatch v (var .v) f f' f'' | yes refl = maybeMatch (var v) 
--                                                  (unifyMaybe (var v) f) 
--                                                  (unifyMaybe (bool F) f') 
--                                                  (unifyMaybe (bool T) f'')
--unifyVarMatch v (var v') f f' f'' | no ¬p = unifyMatchSym (var v) (var v') f f' f'' 
--unifyVarMatch v e f f' f'' = unifyMatchSym (var v) e f f' f'' 
--                                          
--unifyMatchSym u e f f' f'' = maybeMatch e (unifyMaybe u f ) 
--                                          (unifyMaybe u f') 
--                                          (unifyMaybe u f'')
--
----unifyMatchs (var v) f f' f'' (var v') g g' g'' with v ≟ v'
----unifyMatchs (var v) f f' f'' (var .v) g g' g'' | yes refl = just (match (var v) 
----           (unifyMaybeMaybe f g) 
----           (unifyMaybeMaybe f' g') 
----           (unifyMaybeMaybe f'' g''))
----unifyMatchs (var v) f f' f'' (var v') g g' g'' | no ¬p = maybeMatch (var v') 
----  (unifyMaybe (match (var v) f f' f'') g)
----  ?
----  ?
----unifyMatchs e f f' f'' e' g g' g'' = {!!}
--
--unify (bool b) (bool b') = unifyBool b b'
--unify (bool b) (var v) = unifyVarBool v b 
--unify (bool b) (match e f f' f'') = unifyMatchSym (bool b) e f f' f'' 
--unify (var v) (bool b) = unifyVarBool v b
--unify (var v) (var v₁) with v ≟ v₁
--unify (var v) (var .v) | yes refl = just (var v)
--unify (var v) (var v₁) | no ¬p = just (match (var v) nothing (just vF) (just vT))
--  where vF = match (var v₁) nothing (just (bool F)) nothing
--        vT = match (var v₁) nothing nothing (just (bool T))
--unify (var v) (match e' x x₁ x₂) = unifyVarMatch v e' x x₁ x₂
--unify (match e f f' f'') (bool b) = unifyMatchSym (bool b) e f f' f''
--unify (match e f f' f'') (var v) = unifyVarMatch v e f f' f'' 
--unify (match (var v) f f' f'') (match (var v') g g' g'') with v ≟ v'
--unify (match (var v) f f' f'') (match (var .v) g g' g'') | yes refl = just (match (var v) 
--           (unifyMaybeMaybe f g) 
--           (unifyMaybeMaybe f' g') 
--           (unifyMaybeMaybe f'' g''))
--unify (match (var v) f f' f'') (match (var v') g g' g'') | no ¬p = maybeMatch (var v') 
--  (unifyMaybe (match (var v) f f' f'') g) 
--  (unifyMaybe (match (var v) f f' f'') g') 
--  (unifyMaybe (match (var v) f f' f'') g'') 
--unify (match e f f' f'') (match e' g g' g'') = maybeMatch e' 
--  (unifyMaybe (match e f f' f'') g) 
--  (unifyMaybe (match e f f' f'') g')
--  (unifyMaybe (match e f f' f'') g'')
--
--full : {X : ℕ} → Expr X → Full X
--full (bool b) = bool b
--full (if e e' e'') = match (full e) (unify f' f'') (just f') (just f'') -- match {!!} {!!}
--  where f' = full e'
--        f'' = full e''
--full (var v) = var v


