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

  data Color : Set where 
    red green blue : Color 

  private instance 
    _ = green 

  open HasDefault ⦃ ... ⦄ 

open IsEquivalence ⦃ ... ⦄ public 

instance 
  equiv-to-preorder : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {_~_ : Rel A ℓ₂} → ⦃ IsEquivalence _~_ ⦄ → IsPreorder _~_ 
  equiv-to-preorder = isPreorder

  ≡-is-equivalence = ≡-equiv 

module ℕ/nℕ (n : ℕ) where 

  record _≈_ (a b : ℕ) : Set where 
    constructor ≈-mod 
    field 
      x y : ℕ 
      is-mod : a + x * n ≡ b + y * n 
  
  infix 4 _≈_ 

  ≈-refl : Reflexive _≈_ 
  ≈-refl = ≈-mod 0 0 refl 

  ≈-sym : Symmetric _≈_ 
  ≈-sym (≈-mod x y is-mod) = ≈-mod y x (sym is-mod)

  lemma₁ : (a x z : ℕ) → a + (x + z) * n ≡ (a + x * n) + z * n 
  lemma₁ a x z = begin
   a + (x + z) * n ≡⟨ cong (a +_) (*-distribʳ-+ n x z) ⟩
   a + (x * n + z * n) ≡⟨ sym (+-assoc a _ _) ⟩
   a + x * n + z * n
   ∎
   where open ≡-Reasoning

  lemma₂ : (i j k : ℕ) → (i + j) + k ≡ (i + k) + j 
  lemma₂ i j k = begin
   i + j + k ≡⟨ +-assoc i j k ⟩
   i + (j + k) ≡⟨ cong (i +_) (+-comm j k) ⟩
   i + (k + j) ≡⟨ sym (+-assoc i k j) ⟩
   i + k + j
   ∎
   where open ≡-Reasoning
   
  ≈-trans : Transitive _≈_ 
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) = 
    ≈-mod (x + z) (w + y) 
    (begin
     a + (x + z) * n ≡⟨ lemma₁ a x z ⟩
     (a + x * n) + z * n ≡⟨ cong (_+ z * n) pxy ⟩
     (b + y * n) + z * n ≡⟨ lemma₂ b (y * n) (z * n) ⟩
     (b + z * n) + y * n ≡⟨ cong (_+ y * n) pzw ⟩
     (c + w * n) + y * n ≡⟨ sym (lemma₁ c w y) ⟩
     c + (w + y) * n
     ∎)
    where open ≡-Reasoning

  ≈-preorder : IsPreorder _≈_ 
  ≈-preorder .IsPreorder.refl = ≈-refl
  ≈-preorder .IsPreorder.trans = ≈-trans

  ≈-equiv : IsEquivalence _≈_ 
  ≈-equiv .IsEquivalence.isPreorder = ≈-preorder
  ≈-equiv .IsEquivalence.sym = ≈-sym

  instance 
    _ = ≈-equiv 
  
  module Mod-Reasoning where 
    open Preorder-Reasoning ≈-preorder 
      hiding (refl; trans) 
      public 

  0≈n : 0 ≈ n 
  0≈n = ≈-mod 1 0 refl 

  suc-cong-mod : {a b : ℕ} → a ≈ b → suc a ≈ suc b 
  suc-cong-mod (≈-mod x y is-mod) = ≈-mod x y (cong suc is-mod)

  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b 
  +-zero-mod a zero a≈0 = begin
    ? ≡⟨ ? ⟩
    ?
    ∎
    where open Mod-Reasoning 
  +-zero-mod a (suc b) a≈0 = {!   !}


