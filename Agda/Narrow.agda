module Narrow where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Category.Monad
open import Data.Nat
open import Function
open import Data.Empty
open import Relation.Nullary
open import Helpful

--data VarSet : Set where
--  ∅ : VarSet
--  one : VarSet
--  _⊎_ : VarSet → VarSet → VarSet
--  
--data Var : VarSet → Set where
--  here : Var one
--  inL : {X Y : VarSet} → Var X → Var (X ⊎ Y)
--  inR : {X Y : VarSet} → Var Y → Var (X ⊎ Y)
  
record IMonad (I : Set) (M : (I → Set) → (I → Set)) : Set₁ where
   infixr 4 _=<<_ 
   field 
     return : ∀{X i} → X i → M X i
     _=<<_ : ∀{X Y} →  (∀ {i} → X i → M Y i) → ∀ {j} → M X j → M Y j
     ret-left : {i : I}{X Y : I → Set} → (a : X i) → (f : ∀{j} → X j → M Y j) → 
                         f =<< (return a) ≡ f a
     ret-right : ∀{X i} → (m : M X i) → return =<< m ≡ m
     >>=-assoc : ∀{X Y Z i} → (m : M X i) → (f : ∀{j} → X j → M Y j) → 
                                              (g : ∀{j} → Y j → M Z j)
                     → g =<< f =<< m ≡  (λ a → g =<< f a) =<< m
 
                     
module Expression 
                  (T : Set)
                  (E : (T → Set) → (T → Set)) 
                  (monadExp : IMonad T E)
                  (Red : ∀{t X} → E t X → E t X → Set) 
                     where
                     

  _↦_ : ∀{t X} → E t X → E t X → Set
  _↦_ = Red 
  
--  Exp : VarSet → Set
--  Exp X = E (Var X)
  
  infix 3 _↦_

   
  _⇀_ : (T → Set) → (T → Set) → Set
  X ⇀ Y = {t : T} → X t → E Y t
  
  open IMonad monadExp
  
  _>=>_ : ∀{X Y Z} → X ⇀ Y → Y ⇀ Z → X ⇀ Z
  f >=> g = λ x → g =<< f x
  
  _⟦_⟧ : ∀{X Y} →{t : T} → E X t → (∀{u} → X u → E Y u) → E Y t
  e ⟦ σ ⟧ = σ =<< e
  
  infix 100 _⟦_⟧
  
  _⊑_ : ∀{X Y Z} → (X ⇀ Y) → (X ⇀ Z) → Set
  _⊑_ {X}{Y}{Z} σ τ = ∃ (λ (τ' : Y ⇀ Z)  → 
                      _≡_ {A = X ⇀ Z} (σ >=> τ') τ) 
  
  data _↦*_ {t : T}{X : T → Set} : E X t → E X t → Set where
     [] : ∀{e} → e ↦* e
     _:↦:_ : ∀{e e' e''} → e ↦ e' → e' ↦* e'' → e ↦* e''
     
  _↦!_ : {t : T}{X : T → Set} → E X t → E X t → Set 
  _↦!_ {t} {X} e e' = e ↦* e' × ({e'' : E X t} → ¬ (e' ↦ e'')) 
     
--  ↦infinite : (X : T → Set) → Set
--  ↦infinite X =  ∃ (λ (es : ℕ → E X) → (n : ℕ) → es n ↦ es (suc n))
  
  data Terminates {t : T}{X : T → Set} (e : E X t) : Set where
    term : (∀{e'} → e ↦ e' → Terminates e') → Terminates e
    
--  test : ∀{X}{e e' : E X} → ¬ (¬ Terminates e) → e ↦ e' → ¬ (¬ Terminates e')
--  test f r = λ x → f (λ {(term f') → x (f' r)})
--    
--  
--        
  NarrSet :  Set₁
  NarrSet = {t : T} → {X Y : T → Set} → (e : E X t) → (σ : X ⇀ Y) → Set
  
  ∅ : T → Set
  ∅ _ = ⊥

  module Semantics 
    (↦lift : ∀{X Y t}{e e' : E X t} → e ↦ e' → (σ : X ⇀ Y) → e ⟦ σ ⟧  ↦ e' ⟦ σ ⟧ )
    (↦confluent : ∀{X t}{e e₁ e₂ : E X t} → 
                e ↦* e₁ → e ↦* e₂ → Σ (E X t) (λ e' → e₁ ↦* e' × e₂ ↦* e'))
    (↦terminates : ∀{X t} → (e : E X t) → Terminates e)
    (narrSet : NarrSet)
    (⇝set : ∀{X t} → (e : E X t) → (τ : X ⇀ ∅) → 
            (({e' : E ∅ t} → ¬ (e ⟦ τ ⟧ ↦ e')) ⊎
            ∃₃ (λ (Y : T → Set) (σ : X ⇀ Y) (e' : E Y t) → narrSet e σ × σ ⊑ τ × e ⟦ σ ⟧ ↦ e')))
--    (⇝setagrees : ∀{X} → (e : E X) → (τ τ' : X ⇀ ⊥) 
--                           → (proj₁ (proj₂ (⇝set e τ))) ⊑ τ'
--                           → (proj₁ (proj₂ (⇝set e τ'))) ≡ (proj₁ (proj₂ (⇝set e τ'))))
         where 
--         
    deterministic : ∀{X t}{e e' e'' : E X t} → e ↦! e' → e ↦! e'' → e' ≡ e''
    deterministic (r , e'-halted) (r' , e''-halted) with ↦confluent r r'
    deterministic (r , e'-halted) (r' , e''-halted) | e' , [] , [] = refl
    deterministic (r , e'-halted) (r' , e''-halted) | e' , [] , x :↦: r₂ = ⊥-elim (e''-halted x)
    deterministic (r , e'-halted) (r' , e''-halted) | e' , x :↦: r₁ , r₂ = ⊥-elim (e'-halted x)

    lemma-confl : ∀{X t}{e e' e'' : E X t} → e ↦ e' → e ↦! e'' → e' ↦! e''
    lemma-confl r (r' , e''-halted) with ↦confluent (r :↦: []) r'
    lemma-confl r (r' , e''-halted) | e'' , r1 , [] = r1 , e''-halted
    lemma-confl r (r' , e''-halted) | e'' , r1 , x :↦: r2 = ⊥-elim (e''-halted x)
    
    ↦lift-coerce : ∀{X Y Z t}{e : E X t}{e' : E Y t}{σ : X ⇀ Y} → 
                   e ⟦ σ ⟧ ↦ e' → (τ : Y ⇀ Z) → e ⟦ σ >=> τ ⟧ ↦ e' ⟦ τ ⟧ 
    ↦lift-coerce {e = e}{e'}{σ} r τ = subst (λ x → x ↦ e' ⟦ τ ⟧) (>>=-assoc e σ τ) (↦lift r τ)

    record _⇝_ {t : T}{X Y : T → Set} (e : E X t) (ret : E Y t × (X ⇀ Y)) : Set where
      constructor fred 
      field 
         red : e ⟦ proj₂ ret ⟧ ↦  proj₁ ret
         narrRes : narrSet e (proj₂ ret)
         
    data _⇝!_ {t : T} {X Y : T → Set} : E X t → E Y t × X ⇀ Y → Set₁ where
      [] : ∀{e} → (τ : X ⇀ Y) → ({e' : E Y t} → ¬ (e ⟦ τ ⟧ ↦ e')) → e ⇝! (e ⟦ τ ⟧ , τ)
      _:⇝:_ : {Z : T → Set}{e : E X t}{e' : E Z t}{e'' : E Y t}{σ : X ⇀ Z}{σ' : Z ⇀ Y} → 
              e ⇝ (e' , σ) → e' ⇝! (e'' , σ') → e ⇝! (e'' , σ >=> σ')
 
    sound : {t : T}{X Y : T → Set}{e : E X t}{e' : E Y t}{τ : X ⇀ Y} → 
                                           e ⇝! (e' , τ) → e ⟦ τ ⟧ ↦! e'
    sound ([] τ x) = [] , x 
    sound (_:⇝:_ {Z}{e}{e'}{e''}{σ}{σ'} (fred r n) r!) with sound r! 
    ...| r!' , x = ((↦lift-coerce r σ' :↦: r!') , x)
--      where
--       coerce₁ =  subst (λ en → en ↦* e'') (>>=-assoc e σ σ')
--       
    complete' : {t : T}{X : T → Set}{e : E X t}{e' : E ∅ t} → 
              (τ : X ⇀ ∅) → e ⟦ τ ⟧ ↦! e' → Terminates (e ⟦ τ ⟧) → e ⇝! (e' , τ )
    complete' τ ([] , x) t = [] τ x 
    complete' {e = e} τ (r :↦: r! , e'-halted) t with ⇝set e τ 
    complete' {e = e} τ (r :↦: r! , e'-halted) t | inj₁ ¬reducible = ⊥-elim (¬reducible r)
    complete' {e = e} ._ (r :↦: r! , e'-halted) (term t) | inj₂ (Y , σ , e' , o , (τ' , refl) , r') 
         = fred r' o :⇝: complete' τ' (r!' , e'-halted) (t (↦lift-coerce r' τ'))
           where r!' = proj₁ (lemma-confl (↦lift-coerce r' τ') (r :↦: r! , e'-halted))

    complete : {t : T}{X : T → Set}{e : E X t}{e' : E ∅ t} → (τ : X ⇀ ∅) → 
                                          e ⟦ τ ⟧ ↦! e' → e ⇝! (e' , τ )
    complete {e = e} τ r = complete' τ r (↦terminates (e ⟦ τ ⟧))
    
    
    
    

                  
 

          
      --_⇝_ :  
  
