
module Chapter1-Agda where

module Booleans where
  data Bool : Set where   
    false : Bool 
    true  : Bool 

  not : Bool → Bool 
  not false = true
  not true = false

  _∨_ : Bool → Bool → Bool
  true ∨ y = true 
  false ∨ y = y

  _∧_ : Bool → Bool → Bool 
  true ∧ y = y
  false ∧ y = false 

module Example-Employees where 
  open Booleans 
  open import Data.String 
    using (String) 

  data Department : Set where 
    administrative : Department 
    engineering    : Department 
    finance        : Department
    marketing      : Department 
    sales          : Department 

  record Employee : Set where 
    field 
      name        : String
      department  : Department 
      is-new-hire : Bool

  tillman : Employee 
  tillman = record 
    { name        = "Tillman"
    ; department  = engineering 
    ; is-new-hire = false 
    } 

module Sandbox-Tuples where 
  record _×_ (A : Set) (B : Set) : Set where 
    constructor _,_
    field 
      proj₁ : A 
      proj₂ : B 

  open Booleans 
        
  my-tuple : Bool × Bool 
  my-tuple = record { proj₁ = true ∨ true ; proj₂ = not true }

  first : Bool × Bool → Bool 
  first record { proj₁ = x} = x 

  open _×_ 

  my-tuple-first : Bool 
  my-tuple-first = my-tuple .proj₁

  my-tuple-second : Bool 
  my-tuple-second = proj₂ my-tuple

  curry : {A B C : Set} → (A × B → C) → (A → B → C) 
  curry f a b = f (a , b)

  uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry f (a , b) = f a b

  _ : Bool × Bool → Bool
  _ = uncurry _∨_

module Sandbox-Implicits where 
  open import Data.Bool 
    using (Bool; false; true; not; _∨_) 
    
  open import Data.Product 
    using (_×_; proj₁; proj₂) 

    renaming (_,′_ to _,_
             ; curry′ to curry 
             ; uncurry′ to uncurry 
             )

  mk-tuple : (A : Set) → (B : Set) → A → B → A × B 
  mk-tuple A B x x₁ = x , x₁

open import Data.Bool 
  using (Bool; false; true; not; _∨_; _∧_)
  public 

open import Data.Product 
  using (_×_; _,_; proj₁; proj₂; curry; uncurry)
  public 

open import Data.Sum 
  using (_⊎_; inj₁; inj₂) 
  public 


             

  