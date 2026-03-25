module Chapter4-Relations where 

open import Chapter1-Agda 
  using (Bool; false; true; not; _×_) 

open import Chapter2-Numbers 
  using (ℕ; zero; suc; _+_) 

open import Chapter3-Proofs 

open import Agda.Primitive 
  using (Level; _⊔_; lzero; lsuc) 

module Playground-Level where 
  data Maybe₀ (A : Set) : Set where 
    just₀ : A → Maybe₀ A 
    nothing₀ : Maybe₀ A 
    
  data Maybe₁ {ℓ : Level} (A : Set ℓ) : Set ℓ where 
    just₁ : A → Maybe₁ A 
    nothing₁ : Maybe₁ A 

  _ = just₁ ℕ 

  private variable 
    ℓ : Level 

  data Maybe₂ (A : Set ℓ) : Set ℓ where 
    just₂ : A → Maybe₂ A 
    nothing₂ : Maybe₂ A 

private variable 
  ℓ ℓ₁ ℓ₂ a b c : Level 
  A : Set a 
  B : Set b 
  C : Set c 

module Definition-DependentPair where 
  open Chapter3-Proofs 

  record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where 
    constructor _,_ 
    field 
      proj₁ : A 
      proj₂ : B proj₁ 

  -- this won't recognize 4 for some reason
  --∃n,n+1≡ : Σ ℕ (λ n → n + 1 ≡ 5) 
  --∃n,n+1≡ = four, PropEq.refl 

open import Data.Product 
  using (Σ; _,_) 

module Sandbox-Relations where 

  REL : Set a → Set b → (ℓ : Level) 
      → Set (a ⊔ b ⊔ lsuc ℓ) 
  REL A B ℓ = A → B → Set ℓ 

  data Unrelated : REL A B lzero where 

  data Related : REL A B lzero where 
    related : {a : A} {b : B} → Related a b 






  