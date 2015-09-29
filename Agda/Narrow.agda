module Narrow where

open import Data.Product

data VarSet : Set where
  ∅ : VarSet
  one : VarSet
  _⊎_ : VarSet → VarSet → VarSet
  
data Var : VarSet → Set where
  here : Var one
  inL : {X Y : VarSet} → Var X → Var (X ⊎ Y)
  inR : {X Y : VarSet} → Var Y → Var (X ⊎ Y)

 
module Expression (E : VarSet → Set) where
   
  _⇀_ : VarSet → VarSet → Set
  X ⇀ Y = Var X → E Y

  module Semantics (_↦_ : ∀{X} → E X → E X → Set) 
                   (_[_] : ∀{X Y} → E X → X ⇀ Y → E Y )
                   (↦lift : ∀{X Y e e'} → e ↦ e' → (σ : X ⇀ Y) → e [ σ ] ↦ e' [ σ ]  )
                   where
    

    record _⇝_ {X Y : VarSet} (e : E X) (ret : E Y × (X ⇀ Y)) : Set where
      constructor narr 
      field 
         red : e [ proj₂ ret ] ↦  proj₁ ret

      
      --_⇝_ :  
  
