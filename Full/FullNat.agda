module FullNat where

open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (_+_) 
open import Data.Vec hiding (_>>=_) 
--open import Data.Maybe
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Relation.Nullary

data Ty : Set where
  Nat : Ty
  _→ₜ_ : Ty → Ty → Ty

Cxt : ℕ → Set
Cxt = Vec Ty


data Expr {V : ℕ} (Γ : Cxt V) : Ty → Set where
  Z : Expr Γ Nat 
  S : Expr Γ Nat → Expr Γ Nat 
  bot : ∀{t} → Expr Γ t
  ƛ : ∀{u t} → (e : Expr (u ∷ Γ) t) → Expr Γ (u →ₜ t)
  case : ∀{t} → (e : Expr Γ Nat) → (e' : Expr Γ t) → (e'' : Expr Γ (Nat →ₜ t)) → Expr Γ t

  var : ∀{t} → (v : Fin V) → Γ [ v ]= t → Expr Γ t
  app : ∀{u t} → Expr Γ (u →ₜ t) → Expr Γ u → Expr Γ t

data Val {V : ℕ} (Γ : Cxt V) : Ty → Set where
  Z : Val Γ Nat 
  S : Expr Γ Nat → Val Γ Nat 
  bot : ∀{t} → Val Γ t
  ƛ : ∀{u t} → (e : Expr (u ∷ Γ) t) → Val Γ (u →ₜ t)
 

Inp : {V : ℕ} → Cxt V → Set
Inp [] = ⊤
Inp (t ∷ Γ) = Expr Γ t × Inp Γ  

sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucCxt : ∀{V V' u t}{Γ' : Cxt V'}(Γ : Cxt V) → (v : Fin (V + V')) → 
         Γ ++ Γ' [ v ]= t → Γ ++ u ∷ Γ' [ sucVar V v ]= t
sucCxt [] v o = there o
sucCxt (t ∷ Γ) zero here = here
sucCxt (x ∷ Γ) (suc v) (there o) = there (sucCxt Γ v o)

sucExpr : ∀{V V' t u}{Γ' : Cxt V'} → (Γ : Cxt V) → Expr (Γ ++ Γ') t → Expr (Γ ++ u ∷ Γ') t
sucExpr Γ Z = Z
sucExpr Γ (S x) = S (sucExpr Γ x)
sucExpr Γ bot = bot 
sucExpr Γ (ƛ {u = u} e) = ƛ (sucExpr (u ∷ Γ) e)
sucExpr {V = V} Γ (var x o) = var (sucVar V x) (sucCxt Γ x o)
sucExpr Γ (case e e₁ e₂) = case (sucExpr Γ e) (sucExpr Γ e₁) (sucExpr Γ e₂)
sucExpr Γ (app e e₁) = app (sucExpr Γ e) (sucExpr Γ e₁)

substExpr : ∀{V V' t u}{Γ' : Cxt V'}(Γ : Cxt V) → Expr (Γ ++ u ∷ Γ') t → Expr Γ' u → Expr (Γ ++ Γ') t
substExpr Γ Z ef = Z
substExpr Γ (S x) ef = S (substExpr Γ x ef)
substExpr Γ bot ef = bot
substExpr Γ (ƛ {u = u} e) ef = ƛ (substExpr (u ∷ Γ) e ef)
substExpr [] (var zero here) ef = ef 
substExpr [] (var (suc v) (there o)) ef = var v o
substExpr (x ∷ Γ) (var zero here) ef = var zero here
substExpr (x ∷ Γ) (var (suc v) (there o)) ef = sucExpr [] (substExpr Γ (var v o) ef )
substExpr Γ (case e e₁ e₂) ef = case (substExpr Γ e ef) (substExpr Γ e₁ ef) (substExpr Γ e₂ ef)
substExpr Γ (app e e₁) ef = app (substExpr Γ e ef) (substExpr Γ e₁ ef)

_⟪_⟫ : ∀{V u t}{Γ : Cxt V} → Expr (u ∷ Γ) t → Expr Γ u → Expr Γ t
_⟪_⟫ = substExpr [] 

data _↦_ {t : Ty} : Expr [] t → Expr [] t → Set where
  caseSubj : ∀{e e'} → e ↦ e' → ∀{e₁ e₂}  
           → case e e₁ e₂ ↦ case e' e₁ e₂
  caseZ : ∀{e₁ e₂} → case Z e₁ e₂ ↦ e₁
  caseS : ∀{eₛ e₁ e₂} → case (S eₛ) e₁ e₂ ↦ app e₂ eₛ
  casebot : ∀{e₁ e₂} → case bot e₁ e₂ ↦ bot
  appL : ∀{u}{e e' : Expr [] (u →ₜ t)} → e ↦ e' → ∀{e''}  
           → app e e'' ↦ app e' e'' 
  app : ∀{u}{e : Expr [ u ] t}{e' : Expr [] u} → app (ƛ e) e' ↦ e ⟪ e' ⟫
  
data _⇓ₑ_ : {t : Ty} → Expr [] t → Val [] t → Set where
  Z : Z ⇓ₑ Z
  S : ∀{e} → S e ⇓ₑ S e
  bot : ∀{t} → _⇓ₑ_ {t = t} bot bot
  ƛ : ∀{u t}{e : Expr [ u ] t} → ƛ e ⇓ₑ ƛ e
  red : ∀{t e e' e''} → _↦_ {t = t} e e' → e' ⇓ₑ e'' → e ⇓ₑ e''

_⇓ : ∀{t} → Expr [] t → Set
e ⇓ = ∃ (λ v → e ⇓ₑ v)
  

WN' : (t : Ty) → Expr [] t → Set
WN : ∀{t} → Expr [] t → Set

WN {t} e = e ⇓ × WN' t e

WN' Nat e = ⊤
WN' (t₁ →ₜ t₂) e = (e' : Expr [] t₁) → WN e' → WN (app e e')


--WNtoEval : ∀{t V}{Γ : Cxt V}{e : Expr Γ t} →  WN e → e ⇓
--WNtoEval (d , proj₂) = d

apply : ∀{V t}{Γ : Cxt V} → Expr Γ t → Inp Γ → Expr [] t
apply {Γ = []} e s = e
apply {Γ = x ∷ Γ} e (e' , s) = apply (e ⟪ e' ⟫) s

createWN : ∀{V t}{Γ : Cxt V} → (e : Expr Γ t) → (s : Inp Γ) → WN (apply e s)
createWN {Γ = []} Z tt = (Z , Z) , tt
createWN {Γ = x ∷ Γ} Z (e' , s) = createWN Z s
createWN {Γ = []} (S e) s = (S e , S) , tt
createWN {Γ = x ∷ Γ} (S e) (e' , s) with createWN (S (e ⟪ e' ⟫)) s
createWN {._} {.Nat} {x ∷ Γ} (S e) (e' , s) | (proj₁ , proj₂) , proj₃ = ({!!} , {!!}) , {!!} -- (S (apply e (e' , s)) , {!!}) , {!!}
createWN bot s = {!!}
createWN (ƛ e) s = {!!}
createWN (case e e₁ e₂) s = {!!}
createWN (var v x) s = {!!}
createWN (app e e₁) s = {!!}
--createWN Z = (Z , Z) , tt
--createWN (S e) = (S e , S) , tt
--createWN {Nat} bot = (bot , bot) , tt
--createWN {t →ₜ t₁} bot = (bot , bot) , (λ e' x → createWN (app bot e'))  
--createWN (ƛ e) = (ƛ e , ƛ) , (λ e' x → createWN (app (ƛ e) e'))
--createWN (case e e₁ e₂) = {!!}
--createWN (var () x)
--createWN (app e e₁) with createWN e
--...| c  = {!!} 

--evalExpr : ∀{t V}{Γ : Cxt V} → (e : Expr Γ t) → Val Γ t
--evalExpr Z wn = Z
--evalExpr (S e) wn = S e 
--evalExpr bot wn = bot
--evalExpr (case e e₁ e₂) wn with evalExpr e ? 
--evalExpr (case e e₁ e₂) wn | Z = evalExpr e₁ ? 
--evalExpr (case e e₁ e₂) wn | S c = evalExpr (e₂ ⟪ c ⟫) ?
--evalExpr (case e e₁ e₂) wn | bot = bot
--evalExpr (var v o) wn = bot

--data Full (X : ℕ) : Set where
--  val : B → Full X
--  var : (v : Fin X) → Full X
--  match : (Full X) → Full X → Full X → Full X → Full X
--
--  
--basic : {X : ℕ} → Expr X → Full X
--basic (val x) = val x
--basic (if e e' e'') = match (basic e) (val bot) (basic e') (basic e'')
--basic (var x) = var x
--
----evalExpr : {X : ℕ} → Expr X → (Vec B X) → B
----evalExpr (val b) v = b
----evalExpr (if e e' e'') v with evalExpr e v 
----evalExpr (if e e' e'') v | F = evalExpr e' v
----evalExpr (if e e' e'') v | T = evalExpr e'' v
----evalExpr (var x) v = lookup x v 
--
--data _⊑_ : B → B → Set where
--  TT : T ⊑ T
--  FF : F ⊑ F
--  bot : {b : B} → bot ⊑ b
--
--refl-⊑ : ∀{b} → b ⊑ b
--refl-⊑ {T} = TT
--refl-⊑ {F} = FF
--refl-⊑ {bot} = bot
--
--_⊑ₛ_ : {n : ℕ} → Vec B n → Vec B n → Set
--[] ⊑ₛ [] = ⊤
--(x ∷ v) ⊑ₛ (x₁ ∷ v') = (x ⊑ x₁) × (v ⊑ₛ v') 
--
--Monotone : {n : ℕ} → (f : Vec B n → B) → Set
--Monotone {n} f = {v v' : Vec B n} → v ⊑ₛ v' → f v ⊑ f v' 
--
--evalIf : {X : ℕ} → B → Expr X → Expr X → Inp X → B 
--evalExpr : {X : ℕ} → Expr X → Inp X → B 
--
--evalExpr (val b) s = b
--evalExpr (if e e₁ e₂) s = evalIf (evalExpr e s) e₁ e₂ s
--evalExpr (var x) s = lookup x s
--
--evalIf T e e' s = evalExpr e s
--evalIf F e e' s = evalExpr e' s
--evalIf ⊥ e e' s = ⊥ 
--
--monotoneLookup : {X : ℕ} → (v : Fin X) → Monotone (lookup v)
--monotoneLookup zero {x ∷ _} {x₁ ∷ _} (o , _) = o
--monotoneLookup (suc v) {_ ∷ s}{_ ∷ s'} (_ , os) = monotoneLookup v os
--
--monotoneEvalIf : {X : ℕ}{b b' : B}(e e' : Expr X) → (b ⊑ b') → 
--  {v v' : Vec B X} → v ⊑ₛ v' → evalIf b e e' v ⊑ evalIf b' e e' v' 
--
--monotoneEvalExpr : {X : ℕ} → (e : Expr X) → Monotone (evalExpr e)
--monotoneEvalExpr (val b) o = refl-⊑ 
--monotoneEvalExpr (if e e₁ e₂) o = monotoneEvalIf e₁ e₂ (monotoneEvalExpr e o) o
--monotoneEvalExpr (var x) o = monotoneLookup x o
--
--monotoneEvalIf {b = T} e e' TT os = monotoneEvalExpr e os
--monotoneEvalIf {b = F} e e' FF os = monotoneEvalExpr e' os
--monotoneEvalIf {b = bot} e e' bot os = bot
--
--evalMatch : ∀{X} → B → Full X → Full X → Full X → Inp X → B
--evalFull : {X : ℕ} → Full X → Inp X → B
--
--evalFull (val b) s = b
--evalFull (var v) s = lookup v s
--evalFull (match e n et ef) s = evalMatch (evalFull e s) n et ef s
--
--evalMatch T n et ef s = evalFull et s
--evalMatch F n et ef s = evalFull ef s
--evalMatch bot n et ef s = evalFull n s
--
--basicEquiv : ∀{X} → (e : Expr X) → (s : Inp X) → evalExpr e s ≡ evalFull (basic e) s
--basicMatchEquiv : ∀{X} → (b : B) → (e e' : Expr X) → (s : Inp X) 
--    → evalIf b e e' s ≡ evalMatch b (val bot) (basic e) (basic e') s
--
--basicMatchEquiv T e e' s = basicEquiv e s
--basicMatchEquiv F e e' s = basicEquiv e' s
--basicMatchEquiv bot e e' s = refl
--
--basicEquiv (val b) s = refl
--basicEquiv (if e e₁ e₂) s = trans (cong (λ x → evalIf x e₁ e₂ s) (basicEquiv e s)) 
--                                  (basicMatchEquiv (evalFull (basic e) s) e₁ e₂ s) 
--basicEquiv (var v) s = refl
--
--maybeMatch : ∀{X} → Full X → Full X → Full X → Full X → Full X
--maybeMatch e (val bot) (val bot) (val bot) = val bot
--maybeMatch e e' (val bot) (val bot) = e' 
--maybeMatch e f f' f'' = match e f f' f''
--
--sucEq : ∀{N}{m n : Fin N} → _≡_ {A = Fin (suc N)} (suc m) (suc n) → m ≡ n 
--sucEq refl = refl
--
--_≟_ : {N : ℕ} → (m : Fin N) → (n : Fin N) → Dec (m ≡ n) --Dec (m ≡ n)
--zero ≟ zero = yes refl
--zero ≟ suc n₁ = no (λ ())
--suc m ≟ zero = no (λ ())
--suc m ≟ suc n with m ≟ n
--suc m ≟ suc n₁ | yes p = yes (cong suc p)
--suc m ≟ suc n₁ | no ¬p = no (λ x → ¬p (sucEq x))
--
--unifyBool : ∀{X} → B → B → Full X
--unifyBool T T = val T
--unifyBool T F = val bot
--unifyBool T bot = val bot
--unifyBool F T = val bot 
--unifyBool F F = val F
--unifyBool F bot = val bot
--unifyBool bot e' = val bot 

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

