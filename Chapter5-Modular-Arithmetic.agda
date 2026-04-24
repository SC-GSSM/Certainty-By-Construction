module Chapter5-Modular-Arithmetic where 

open import Chapter1-Agda 
open import Chapter2-Numbers
open import Chapter3-Proofs 
open PropEq using (cong) 
open import Chapter4-Relations 

module Playground-Instances where 
  open PropEq 

  default : {ℓ : Level} {A : Set ℓ} → ⦃ a : A ⦄ → A 
  default ⦃ val ⦄ = val 

  private instance
    default-ℕ : ℕ 
    default-ℕ = 0 

    default-Bool : Bool 
    default-Bool = false 

  _ : default ≡ 0 
  _ = PropEq.refl 

  _ : default ≡ false 
  _ = PropEq.refl 

  private instance 
    find-z≤n : {n : ℕ} → 0 ≤ n 
    find-z≤n = z≤n 

    find-s≤n : {m n : ℕ} → ⦃ m ≤ n ⦄ → suc m ≤ suc n 
    find-s≤n ⦃ m≤n ⦄ = s≤s m≤n

  _ : 10 ≤ 20 
  _ = default 

module Playground-Instances₂ where 

  record HasDefault {ℓ : Level} (A : Set ℓ) : Set ℓ where 
    constructor default-of 
    field 
      the-default : A 

  default : {ℓ : Level} {A : Set ℓ} → ⦃ HasDefault A ⦄ → A 
  default ⦃ default-of val ⦄ = val 

  private instance 
    _ = default-of 0 
    _ = default-of false 


