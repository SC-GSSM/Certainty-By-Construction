module Chapter3-Proofs where

open import Chapter1-Agda 
  using (Bool; true; false; _∨_; _∧_; not) 

open import Chapter2-Numbers 
  using (ℕ; zero; suc) 

module Example-ProofsAsPrograms where 
  open Chapter2-Numbers 
    using (ℕ; IsEven) 
  
  open ℕ 
  open IsEven 

  zero-is-even : IsEven zero 
  zero-is-even = zero-even 

module Definition where 
  data _≡_ {A : Set} : A → A → Set where 
    refl : {x : A} → x ≡ x 

  infix 4 _≡_ 

module Playground where 
  open import Relation.Binary.PropositionalEquality 
    using (_≡_; refl) 

  open Chapter2-Numbers

  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl 

  _ : three ≡ suc (suc (suc zero)) 
  _ = refl 

  _ : three ≡ one + two 
  _ = refl 

  0+x≡x : (x : ℕ) → zero + x ≡ x 
  0+x≡x _ = refl 

  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y 
  cong f refl = refl

  x+0≡x : (x : ℕ) → x + zero ≡ x 
  x+0≡x zero = refl
  x+0≡x (suc x) = cong suc (x+0≡x x)

  +-identityˡ  : (x : ℕ) → zero + x ≡ x 
  +-identityˡ = 0+x≡x 

  +-identityʳ : (x : ℕ) → x + zero ≡ x 
  +-identityʳ = x+0≡x 

  *-identityˡ : (x : ℕ) → 1 * x ≡ x 
  *-identityˡ zero = refl
  *-identityˡ (suc x) = cong suc (+-identityʳ x)

  *-identityʳ : (x : ℕ) → x * 1 ≡ x 
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  ∸-identityʳ : (x : ℕ) → x ∸ 0 ≡ x 
  ∸-identityʳ _ = refl 

  ^-identityʳ : (x : ℕ) → x ^ 1 ≡ x 
  ^-identityʳ zero = refl
  ^-identityʳ (suc x) = cong suc (^-identityʳ x)

  ∨-identityˡ : (b : Bool) → false ∨ b ≡ b 
  ∨-identityˡ _ = refl

  ∨-identityʳ : (b : Bool) → b ∨ false ≡ b 
  ∨-identityʳ false = refl
  ∨-identityʳ true = refl 

  ∧-identityˡ : (b : Bool) → true ∧ b ≡ b 
  ∧-identityˡ _ = refl

  ∧-identityʳ : (b : Bool) → b ∧ true ≡ b 
  ∧-identityʳ false = refl
  ∧-identityʳ true = refl

  *-zeroˡ : (x : ℕ) → zero * x ≡ zero 
  *-zeroˡ x = refl 

  *-zeroʳ : (x : ℕ) → x * zero ≡ zero 
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x 

  ∨-zeroˡ : (b : Bool) → true ∨ b ≡ true 
  ∨-zeroˡ b = refl

  ∨-zeroʳ : (b : Bool) → b ∨ true ≡ true 
  ∨-zeroʳ false = refl
  ∨-zeroʳ true = refl

  ∧-zeroˡ : (b : Bool) → false ∧ b ≡ false 
  ∧-zeroˡ _ = refl 

  ∧-zeroʳ : (b : Bool) → b ∧ false ≡ false 
  ∧-zeroʳ false = refl
  ∧-zeroʳ true = refl

  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x 
  sym refl = refl 

  *-identityˡ′ : (x : ℕ) → x ≡ 1 * x 
  *-identityˡ′ x = sym (*-identityˡ x)

  sym-involutive : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p 
  sym-involutive refl = refl

  not-involutive : (x : Bool) → not (not x) ≡ x 
  not-involutive false = refl
  not-involutive true = refl

  trans : {A : Set} {x y z : Set} → x ≡ y → y ≡ z → x ≡ z 
  trans refl refl = refl

  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + b * 0 
  a^1≡a+b*0 a b = {!   !}