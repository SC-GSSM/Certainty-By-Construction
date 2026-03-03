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