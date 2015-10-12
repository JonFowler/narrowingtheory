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
  
record Monad (M : (Set → Set)) : Set₁ where
   infixl 4 _>>=_ 
   field 
     return : ∀{X : Set} → X → M X
     _>>=_ : ∀{X Y : Set} → M X → (X → M Y) → M Y
     ret-left : ∀{X Y} → (a : X) → (f : X → M Y) → 
                         return a >>= f ≡ f a
     ret-right : ∀{X } → (m : M X) → m >>= return ≡ m
     >>=-assoc : ∀{X Y Z} → (m : M X) → (f : X → M Y) → (g : Y → M Z)
                     → m >>= f >>= g ≡ m >>= (λ a → f a >>= g)
 
                     
module Expression 
                  (E : Set → Set) 
                  (monadExp : Monad E)
                  (Red : ∀{X} → E X → E X → Set) 
                     where
                     

  _↦_ : ∀{X} → E X → E X → Set
  _↦_ = Red 
  
--  Exp : VarSet → Set
--  Exp X = E (Var X)
  
  infix 3 _↦_

   
  _⇀_ : Set → Set → Set
  X ⇀ Y =  X → E Y
  
  open Monad monadExp
  
  _>=>_ : ∀{X Y Z} → X ⇀ Y → Y ⇀ Z → X ⇀ Z
  f >=> g = λ x → f x >>= g
  
  _⟦_⟧ : ∀{X Y} → E X → (X → E Y) → E Y
  _⟦_⟧ = _>>=_
  
  infix 100 _⟦_⟧
  
  _⊑_ : ∀{X Y Z} → (X ⇀ Y) → (X ⇀ Z) → Set
  σ ⊑ τ = ∃ (λ τ' → σ >=> τ' ≡ τ )
  
  data _↦*_ {X : Set} : E X → E X → Set where
     [] : ∀{e} → e ↦* e
     _:↦:_ : ∀{e e' e''} → e ↦ e' → e' ↦* e'' → e ↦* e''
     
  _↦!_ : {X : Set} → E X → E X → Set 
  _↦!_ {X} e e' = e ↦* e' × ({e'' : E X} → ¬ (e' ↦ e'')) 
     
  ↦infinite : (X : Set) → Set
  ↦infinite X =  ∃ (λ (es : ℕ → E X) → (n : ℕ) → es n ↦ es (suc n))
  
  data Terminates {X : Set} (e : E X) : Set where
    term : (∀{e'} → e ↦ e' → Terminates e') → Terminates e
    
  test : ∀{X}{e e' : E X} → ¬ (¬ Terminates e) → e ↦ e' → ¬ (¬ Terminates e')
  test f r = λ x → f (λ {(term f') → x (f' r)})
    
  
        
  NarrSet :  Set₁
  NarrSet = {X Y : Set} → (e : E X) → (σ : X ⇀ Y) → Set

  module Semantics 
    (↦lift : ∀{X Y e e'} → e ↦ e' → (σ : X ⇀ Y) → e ⟦ σ ⟧  ↦ e' ⟦ σ ⟧ )
    (↦confluent : ∀{X e e₁ e₂}  → e ↦* e₁ → e ↦* e₂ → Σ (E X) (λ e' → e₁ ↦* e' × e₂ ↦* e'))
    (↦terminates : {X : Set} → (e : E X) → Terminates e)
    (narrSet : NarrSet)
    (⇝set : ∀{X} → (e : E X) → (τ : X ⇀ ⊥) → 
            (({e' : E ⊥} → ¬ (e ⟦ τ ⟧ ↦ e')) ⊎
            ∃₃ (λ (Y : Set) (σ : X ⇀ Y) (e' : E Y) → narrSet e σ × σ ⊑ τ × e ⟦ σ ⟧ ↦ e')))
--    (⇝setagrees : ∀{X} → (e : E X) → (τ τ' : X ⇀ ⊥) 
--                           → (proj₁ (proj₂ (⇝set e τ))) ⊑ τ'
--                           → (proj₁ (proj₂ (⇝set e τ'))) ≡ (proj₁ (proj₂ (⇝set e τ'))))
         where 
         
    deterministic : ∀{X}{e e' e'' : E X} → e ↦! e' → e ↦! e'' → e' ≡ e''
    deterministic (r , e'-halted) (r' , e''-halted) with ↦confluent r r'
    deterministic (r , e'-halted) (r' , e''-halted) | e' , [] , [] = refl
    deterministic (r , e'-halted) (r' , e''-halted) | e' , [] , x :↦: r₂ = ⊥-elim (e''-halted x)
    deterministic (r , e'-halted) (r' , e''-halted) | e' , x :↦: r₁ , r₂ = ⊥-elim (e'-halted x)

    lemma-confl : ∀{X}{e e' e'' : E X} → e ↦ e' → e ↦! e'' → e' ↦! e''
    lemma-confl r (r' , e''-halted) with ↦confluent (r :↦: []) r'
    lemma-confl r (r' , e''-halted) | e'' , r1 , [] = r1 , e''-halted
    lemma-confl r (r' , e''-halted) | e'' , r1 , x :↦: r2 = ⊥-elim (e''-halted x)
    

    ↦lift-coerce : ∀{X Y Z}{e : E X}{e' : E Y}{σ : X ⇀ Y} → 
                   e ⟦ σ ⟧ ↦ e' → (τ : Y ⇀ Z) → e ⟦ σ >=> τ ⟧ ↦ e' ⟦ τ ⟧ 
    ↦lift-coerce {e = e}{e'}{σ} r τ = subst (λ x → x ↦ e' ⟦ τ ⟧) (>>=-assoc e σ τ) (↦lift r τ)

    record _⇝_ {X Y : Set} (e : E X) (ret : E Y × (X ⇀ Y)) : Set where
      constructor fred 
      field 
         red : e ⟦ proj₂ ret ⟧ ↦  proj₁ ret
         narrRes : narrSet e (proj₂ ret)
         
    data _⇝!_ {X Y : Set} : E X → E Y × X ⇀ Y → Set₁ where
      [] : ∀{e} → (τ : X ⇀ Y) → ({e' : E Y} → ¬ (e ⟦ τ ⟧ ↦ e')) → e ⇝! (e ⟦ τ ⟧ , τ)
      _:⇝:_ : {Z : Set}{e : E X}{e' : E Z}{e'' : E Y}{σ : X ⇀ Z}{σ' : Z ⇀ Y} → 
              e ⇝ (e' , σ) → e' ⇝! (e'' , σ') → e ⇝! (e'' , σ >=> σ')
 
    sound : {X Y : Set}{e : E X}{e' : E Y}{τ : X ⇀ Y} → e ⇝! (e' , τ) → e ⟦ τ ⟧ ↦! e'
    sound ([] τ x) = [] , x 
    sound (_:⇝:_ {Z}{e}{e'}{e''}{σ}{σ'} (fred r n) r!) with sound r! 
    ...| r!' , x = ((↦lift-coerce r σ' :↦: r!') , x)
      where
       coerce₁ =  subst (λ en → en ↦* e'') (>>=-assoc e σ σ')
       
    complete' : {X : Set}{e : E X}{e' : E ⊥} → (τ : X ⇀ ⊥) → e ⟦ τ ⟧ ↦! e' → Terminates (e ⟦ τ ⟧) → e ⇝! (e' , τ )
    complete' τ ([] , x) t = [] τ x 
    complete' {e = e} τ (r :↦: r! , e'-halted) t with ⇝set e τ 
    complete' {e = e} τ (r :↦: r! , e'-halted) t | inj₁ ¬reducible = ⊥-elim (¬reducible r)
    complete' {e = e} ._ (r :↦: r! , e'-halted) (term t) | inj₂ (Y , σ , e' , o , (τ' , refl) , r') 
         = fred r' o :⇝: complete' τ' (r!' , e'-halted) (t (↦lift-coerce r' τ'))
           where r!' = proj₁ (lemma-confl (↦lift-coerce r' τ') (r :↦: r! , e'-halted))

    complete : {X : Set}{e : E X}{e' : E ⊥} → (τ : X ⇀ ⊥) → e ⟦ τ ⟧ ↦! e' → e ⇝! (e' , τ )
    complete {e = e} τ r = complete' τ r (↦terminates (e ⟦ τ ⟧))
    
    
    
    

                  
 

          
      --_⇝_ :  
  
