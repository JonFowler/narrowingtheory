module FullNat where

open import Coinduction
open import Data.Nat hiding (_≟_) hiding (_*_)
open import Data.Fin hiding (_+_) 
--open import Data.Vec hiding (_>>=_) 
--open import Data.Maybe
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Relation.Nullary

data Ty : Set where
  Nat : Ty
  _→ₜ_ : Ty → Ty → Ty

data Cxt : Set where
  ε : Cxt
  _,_ : Cxt → Ty → Cxt
  
data _∈_ (t : Ty) : Cxt → Set where
  here : ∀{Γ} → t ∈ Γ , t
  there : ∀{u Γ} → t ∈ Γ → t ∈ Γ , u
infix 3 _∈_ 

data Term (Γ : Cxt) : Ty → Set where
  Z : Term Γ Nat 
  S : Term Γ Nat → Term Γ Nat 
  bot : ∀{t} → Term Γ t
  ƛ : ∀{u t} → (e : Term (Γ , u) t) → Term Γ (u →ₜ t)
  case : ∀{t} → (e : Term Γ Nat) → (e' : Term Γ t) → (e'' : Term Γ (Nat →ₜ t)) → Term Γ t

  var : ∀{t} → (v : t ∈ Γ) → Term Γ t
  app : ∀{u t} → Term Γ (u →ₜ t) → Term Γ u → Term Γ t

data Val (Γ : Cxt) : Ty → Set where
  Z : Val Γ Nat 
  S : ∞ (Val Γ Nat) → Val Γ Nat 
  bot : ∀{t} → Val Γ t
  ƛ : ∀{u t} → (e : Term (Γ , u) t) → Val Γ (u →ₜ t)
 
data Inp : Cxt → Set where
  [] : Inp ε 
  _,_ : ∀{t Γ} → Inp Γ → Term Γ t → Inp (Γ , t)




Ren : Cxt → Cxt → Set
Ren Γ Γ′ = ∀ {τ} → τ ∈ Γ → τ ∈ Γ′

extend' : ∀ {Γ Γ′ τ′} → Ren Γ Γ′ → Ren (Γ , τ′) (Γ′  , τ′)
extend' f here = here
extend' f (there x) = there (f x)

_*'_ : ∀ {Γ Γ′ : Cxt} {τ} → Ren Γ Γ′ → Term Γ τ → Term Γ′ τ
r *' Z = Z
r *' S e = S (r *' e)
r *' bot = bot
r *' ƛ e = ƛ (extend' r *' e)
r *' case e e₁ e₂ = case (r *' e) (r *' e₁) (r *' e₂)
r *' var v = var (r v)
r *' app e e₁ = app (r *' e) (r *' e₁)

-- A substitution from Γ to Γ′.
Sub : Cxt → Cxt → Set
Sub Γ Γ′ = ∀ {τ} → τ ∈ Γ → Term Γ′ τ

extend : ∀ {Γ Γ′ τ} → Sub Γ Γ′ → Sub (Γ , τ) (Γ′ , τ)
extend θ here = var here
extend θ (there x) = there *' θ x

_*_ : ∀ {Γ Γ′ : Cxt} {τ} → Sub Γ Γ′ → Term Γ τ → Term Γ′ τ
f * Z = Z
f * S e = S (f * e)
f * bot = bot
f * ƛ e = ƛ (extend f * e)
f * case e e₁ e₂ = case (f * e) (f * e₁) (f * e₂)
f * var v = f v
f * app e e₁ = app (f * e) (f * e₁)

sub : ∀{t Γ} → Term Γ t → Sub (Γ , t) Γ
sub e here = e
sub e (there v) = var v

_⟨_⟩ : ∀{Γ u t} → Term (Γ , u) t → Term Γ u → Term Γ t 
f ⟨ e ⟩ = sub e * f

--_⟪_⟫ : ∀{V u t}{Γ : Cxt V} → Term (u ∷ Γ) t → Term Γ u → Term Γ t
--_⟪_⟫ = substTerm [] 
--
data _↦_ {Γ : Cxt}{t : Ty} : Term Γ t → Term Γ t → Set where
  caseSubj : ∀{e e'} → e ↦ e' → ∀{e₁ e₂}  
           → case e e₁ e₂ ↦ case e' e₁ e₂
  caseZ : ∀{e₁ e₂} → case Z e₁ e₂ ↦ e₁
  caseS : ∀{eₛ e₁ e₂} → case (S eₛ) e₁ e₂ ↦ app e₂ eₛ
  casebot : ∀{e₁ e₂} → case bot e₁ e₂ ↦ bot
  appL : ∀{u}{e e' : Term Γ (u →ₜ t)} → e ↦ e' → ∀{e''}  
           → app e e'' ↦ app e' e'' 
  app : ∀{u}{e : Term (Γ , u) t}{e' : Term Γ u} → app (ƛ e) e' ↦ e ⟨ e' ⟩
  
data _⇓ {Γ : Cxt} : {t : Ty} → Term Γ t → Set where
  Z : Z ⇓ 
  S : ∀{e} → ∞ (e ⇓) → S e ⇓
  bot : ∀{t} → _⇓ {t = t} bot 
  ƛ : ∀{u t}{e : Term (Γ , u) t} → ƛ e ⇓ 
  red : ∀{t e e'} → _↦_ {t = t} e e' → e' ⇓ → e ⇓ 
  
evalVal : ∀{Γ t} {e : Term Γ t} → e ⇓ → Val Γ t
evalVal Z = Z
evalVal (S x) = S (♯ evalVal (♭ x))
evalVal bot = bot
evalVal {e = ƛ e} ƛ = ƛ e
evalVal (red x re) = evalVal re


WN' : ∀ Γ t → Term Γ t → Set
WN : ∀{Γ t} → Term Γ t → Set

WN {Γ}{t} e = e ⇓ × WN' Γ t e

WN' Γ Nat e = ⊤
WN' Γ (t₁ →ₜ t₂) e = (e' : Term Γ t₁) → WN e' → WN (app e e')

----WNtoEval : ∀{t V}{Γ : Cxt V}{e : Term Γ t} →  WN e → e ⇓
----WNtoEval (d , proj₂) = d
--

subInp : ∀{Γ} → Inp Γ → Sub Γ ε
subInp [] ()
subInp (es , e) here = subInp es * e
subInp (es , e) (there v) = subInp es v

WNInp : ∀{Γ} → Inp Γ → Set
WNInp [] = ⊤
WNInp (es , e) = WNInp es × WN e


subInp-refl : ∀{t} → (e : Term ε t) → subInp [] * e ≡ e
subInp-refl Z = refl
subInp-refl (S e) = cong S (subInp-refl e)
subInp-refl bot = refl
subInp-refl (ƛ e) = cong ƛ {!!}
subInp-refl (case e e₁ e₂) = {!!}
subInp-refl (var v) = {!!}
subInp-refl (app e e₁) = {!!}

apply : ∀{t Γ} → Term Γ t → Inp Γ → Term ε t
apply e es = subInp es * e 

--test : ∀{Γ} (e : Term Γ Nat) → e ⇓ → S e ⇓
--test e (v , r) = S {!!} , S (♯ r) -- S {!!} -- {!!} , {!!}

createWN : ∀{t Γ} → (e : Term Γ t) → (s : Inp Γ) → WN (apply e s)
createWN Z s = Z , tt
createWN (S e) s = (S (♯ proj₁ (createWN e s))) , tt 
createWN {t = Nat} bot s = bot , tt
createWN {t = t₁ →ₜ t₂} bot s = bot , (λ e' x → createWN (app bot {!e'!}) [])
createWN (ƛ e) s = {!!}
createWN (case e e₁ e₂) s = {!!}
createWN (var v) s = {!!}
createWN (app e e₁) s = {!!}


--createWN {Γ = []} Z tt = (Z , Z) , tt
--createWN {Γ = x ∷ Γ} Z (e' , s) = createWN Z s
--createWN {Γ = []} (S e) s = (S e , S) , tt
--createWN {Γ = x ∷ Γ} (S e) (e' , s) with createWN (S (e ⟪ e' ⟫)) s
--createWN {._} {.Nat} {x ∷ Γ} (S e) (e' , s) | (proj₁ , proj₂) , proj₃ = ({!!} , {!!}) , {!!} -- (S (apply e (e' , s)) , {!!}) , {!!}
--createWN bot s = {!!}
--createWN (ƛ e) s = {!!}
--createWN (case e e₁ e₂) s = {!!}
--createWN (var v x) s = {!!}
--createWN (app e e₁) s = {!!}
--createWN Z = (Z , Z) , tt
--createWN (S e) = (S e , S) , tt
--createWN {Nat} bot = (bot , bot) , tt
--createWN {t →ₜ t₁} bot = (bot , bot) , (λ e' x → createWN (app bot e'))  
--createWN (ƛ e) = (ƛ e , ƛ) , (λ e' x → createWN (app (ƛ e) e'))
--createWN (case e e₁ e₂) = {!!}
--createWN (var () x)
--createWN (app e e₁) with createWN e
--...| c  = {!!} 

--evalTerm : ∀{t V}{Γ : Cxt V} → (e : Term Γ t) → Val Γ t
--evalTerm Z wn = Z
--evalTerm (S e) wn = S e 
--evalTerm bot wn = bot
--evalTerm (case e e₁ e₂) wn with evalTerm e ? 
--evalTerm (case e e₁ e₂) wn | Z = evalTerm e₁ ? 
--evalTerm (case e e₁ e₂) wn | S c = evalTerm (e₂ ⟪ c ⟫) ?
--evalTerm (case e e₁ e₂) wn | bot = bot
--evalTerm (var v o) wn = bot

--data Full (X : ℕ) : Set where
--  val : B → Full X
--  var : (v : Fin X) → Full X
--  match : (Full X) → Full X → Full X → Full X → Full X
--
--  
--basic : {X : ℕ} → Term X → Full X
--basic (val x) = val x
--basic (if e e' e'') = match (basic e) (val bot) (basic e') (basic e'')
--basic (var x) = var x
--
----evalTerm : {X : ℕ} → Term X → (Vec B X) → B
----evalTerm (val b) v = b
----evalTerm (if e e' e'') v with evalTerm e v 
----evalTerm (if e e' e'') v | F = evalTerm e' v
----evalTerm (if e e' e'') v | T = evalTerm e'' v
----evalTerm (var x) v = lookup x v 
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
--evalIf : {X : ℕ} → B → Term X → Term X → Inp X → B 
--evalTerm : {X : ℕ} → Term X → Inp X → B 
--
--evalTerm (val b) s = b
--evalTerm (if e e₁ e₂) s = evalIf (evalTerm e s) e₁ e₂ s
--evalTerm (var x) s = lookup x s
--
--evalIf T e e' s = evalTerm e s
--evalIf F e e' s = evalTerm e' s
--evalIf ⊥ e e' s = ⊥ 
--
--monotoneLookup : {X : ℕ} → (v : Fin X) → Monotone (lookup v)
--monotoneLookup zero {x ∷ _} {x₁ ∷ _} (o , _) = o
--monotoneLookup (suc v) {_ ∷ s}{_ ∷ s'} (_ , os) = monotoneLookup v os
--
--monotoneEvalIf : {X : ℕ}{b b' : B}(e e' : Term X) → (b ⊑ b') → 
--  {v v' : Vec B X} → v ⊑ₛ v' → evalIf b e e' v ⊑ evalIf b' e e' v' 
--
--monotoneEvalTerm : {X : ℕ} → (e : Term X) → Monotone (evalTerm e)
--monotoneEvalTerm (val b) o = refl-⊑ 
--monotoneEvalTerm (if e e₁ e₂) o = monotoneEvalIf e₁ e₂ (monotoneEvalTerm e o) o
--monotoneEvalTerm (var x) o = monotoneLookup x o
--
--monotoneEvalIf {b = T} e e' TT os = monotoneEvalTerm e os
--monotoneEvalIf {b = F} e e' FF os = monotoneEvalTerm e' os
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
--basicEquiv : ∀{X} → (e : Term X) → (s : Inp X) → evalTerm e s ≡ evalFull (basic e) s
--basicMatchEquiv : ∀{X} → (b : B) → (e e' : Term X) → (s : Inp X) 
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
--full : {X : ℕ} → Term X → Full X
--full (bool b) = bool b
--full (if e e' e'') = match (full e) (unify f' f'') (just f') (just f'') -- match {!!} {!!}
--  where f' = full e'
--        f'' = full e''
--full (var v) = var v

