module Narrow where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Category.Monad

data VarSet : Set where
  ∅ : VarSet
  one : VarSet
  _⊎_ : VarSet → VarSet → VarSet
  
data Var : VarSet → Set where
  here : Var one
  inL : {X Y : VarSet} → Var X → Var (X ⊎ Y)
  inR : {X Y : VarSet} → Var Y → Var (X ⊎ Y)
  
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
  
  infix 1 _↦_

   
  _⇀_ : VarSet → VarSet → Set
  X ⇀ Y = Var X → E (Var Y) 
  
  open Monad monadExp
  
  _>=>_ : ∀{X Y Z} → X ⇀ Y → Y ⇀ Z → X ⇀ Z
  f >=> g = λ x → f x >>= g
  
  _⟦_⟧ : ∀{X Y} → E X → (X → E Y) → E Y
  _⟦_⟧ = _>>=_
  
  _⊑_ : ∀{X Y Z} → (X ⇀ Y) → (X ⇀ Z) → Set
  σ ⊑ τ = ∃ (λ τ' → σ >=> τ' ≡ τ )
  
  data _↦*_ {X : Set} : E X → E X → Set where
     [] : ∀{e} → e ↦* e
     _:↦_ : ∀{e e' e''} → e ↦ e' → e' ↦* e'' → e ↦* e''


  module Semantics (↦lift : ∀{X Y e e'} → e ↦ e' → (σ : X ⇀ Y) → 
                                      e ⟦ σ ⟧  ↦ e' ⟦ σ ⟧ )
         where 
                 
    
    

--                  
-- 
--
--    record _⇝_ {X Y : VarSet} (e : E X) (ret : E Y × (X ⇀ Y)) : Set where
--      constructor narr 
--      field 
--         red : e [ proj₂ ret ] ↦  proj₁ ret

      
      --_⇝_ :  
  
