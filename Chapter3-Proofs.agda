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
  ^-identityʳ (suc x) = cong suc (*-identityʳ x)

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

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z 
  trans refl refl = refl

  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + b * 0 
  a^1≡a+b*0 a b = trans (^-identityʳ a) (trans (sym (+-identityʳ a)) (cong (a +_) (sym (*-zeroʳ b))))

  _! : ℕ → ℕ 
  zero ! = 1
  suc x ! = suc x * x

  ∣_ : ℕ → ℕ 
  ∣_ = suc 

  infixr 20 ∣_ 

  --five : ℕ 
  --five = ∣ ∣ ∣ ∣ ∣ zero 

  ■ : ℕ 
  ■ = zero 

  five : ℕ 
  five = ∣ ∣ ∣ ∣ ∣ ■ 

  postulate 
    ℝ : Set 
    π : ℝ 
    ⌊_⌋ : ℝ → ℕ 

  three′ : ℕ 
  three′ = ⌊ π ⌋

  _‽_⦂_ : {A : Set} → Bool → A → A → A 
  false ‽ t ⦂ f = f
  true ‽ t ⦂ f = t

  infixr 20 _‽_⦂_ 

  if_then_else_ : {A : Set} → Bool → A → A → A 
  if_then_else_ = _‽_⦂_ 

  infixr 20 if_then_else_ 

  case_of_ : {A B : Set} → A → (A → B) → B 
  case e of f =  f e 

  _is-equal-to_ : {A : Set} → A → A → Set 
  x is-equal-to y = x ≡ y 

  module ≡-Reasoning where 

    _∎ : {A : Set} → (x : A) → x ≡ x 
    _∎ x = refl 

    infix 3 _∎ 

    _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y 
    x ≡⟨⟩ p = p 

    infixr 2 _≡⟨⟩_

    _ : four ≡ suc (one + two) 
    _ = four            ≡⟨⟩ 
        two + two       ≡⟨⟩ 
        suc one + two   ≡⟨⟩ 
        suc (one + two) ≡⟨⟩ 
        suc three       ∎ 

    _≡⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z 
    x ≡⟨ j ⟩ p = trans j p

    infixr 2 _≡⟨_⟩_

    _by_equals_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z 
    _by_equals_ = _≡⟨_⟩_

    infixr 2 _by_equals_

    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y 
    begin_ hyp = hyp 

    infix 1 begin_ 

  a^1≡a+b*0′ : (a b : ℕ) → a ^ 1 ≡ a + b * 0 
  a^1≡a+b*0′ a b = 
    begin 
      a ^ 1 by ^-identityʳ a equals  
      a     ≡⟨ sym (+-identityʳ a) ⟩ 
      a + 0 ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩ 
      a + b * 0 
      ∎
    where open ≡-Reasoning 

  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c) 
  ∨-assoc false b c = refl
  ∨-assoc true b c = refl

  ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c) 
  ∧-assoc false b c = refl
  ∧-assoc true b c = refl

  +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z =
    begin
     suc x + y + z ≡⟨⟩ 
     suc (x + y + z) ≡⟨ cong suc (+-assoc x y z) ⟩
     suc (x + (y + z)) ≡⟨⟩ 
     suc x + (y + z)
     ∎
    where open ≡-Reasoning

  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y) 
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  -- this is not necessary because agda auto resolves it 
  suc-+ : (x y : ℕ) → suc x + y ≡ suc (x + y) 
  suc-+ x y = refl

  +-comm : (x y : ℕ) → x + y ≡ y + x 
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc x) y = 
    begin
     suc x + y by cong suc (+-comm x y) equals 
     suc (y + x) by sym (+-suc y x) equals
     y + suc x
     ∎
    where open ≡-Reasoning

  suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y 
  suc-injective refl = refl

  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y 
  *-suc zero y = refl
  *-suc (suc x) y = 
    begin
     suc x * suc y ≡⟨⟩
     suc y + x * suc y by cong (λ t → suc y + t) (*-suc x y) equals
     suc y + (x + x * y) ≡⟨⟩ 
     suc (y + (x + x * y)) by cong suc (sym (+-assoc y x (x * y))) equals
     suc ((y + x) + x * y) by cong suc (cong (λ t → t + (x * y)) (+-comm y x)) equals
     suc ((x + y) + x * y) by cong suc (+-assoc x y (x * y)) equals
     suc (x + (y + x * y)) ≡⟨⟩ 
     suc x + suc x * y
     ∎
    where open ≡-Reasoning

  *-comm : (x y : ℕ) → x * y ≡ y * x 
  *-comm zero y = sym (*-zeroʳ y)
  *-comm (suc x) y = 
    begin
     (suc x * y) ≡⟨⟩ 
     (y + x * y) by cong (λ t → y + t) (*-comm x y) equals
     (y + y * x) by sym(*-suc y x) equals
     (y * suc x)
     ∎
    where open ≡-Reasoning 

  *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x 
  *-distribʳ-+ x zero z = refl
  *-distribʳ-+ x (suc y) z = 
    begin
     ((suc y + z) * x) ≡⟨⟩
     ((suc (y + z)) * x) ≡⟨⟩ 
     (x + ((y + z) * x)) by cong (λ t → x + t) (*-distribʳ-+ x y z) equals
     (x + (y * x + z * x)) by sym (+-assoc x (y * x) (z * x)) equals
     ((x + y * x) + z * x) ≡⟨⟩
     (suc y * x + z * x)
     ∎
    where open ≡-Reasoning

  *-distribˡ-+ : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z 
  *-distribˡ-+ x y z = 
    begin
     (x * (y + z)) by *-comm x _ equals 
     ((y + z) * x) by *-distribʳ-+ x y z equals
     (y * x + z * x) by cong (λ t → t + z * x) (sym (*-comm x y)) equals 
     (x * y + z * x) by cong (λ t → x * y + t) (sym (*-comm x z)) equals
     (x * y + x * z)
     ∎
    where open ≡-Reasoning 

  *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z) 
  *-assoc zero y z = refl
  *-assoc (suc x) y z = 
    begin
     suc x * y * z ≡⟨⟩
     (y + x * y) * z by *-distribʳ-+ z y (x * y) equals
     y * z + (x * y) * z by cong (λ t → y * z + t) (*-assoc x y z) equals
     y * z + x * (y * z) ≡⟨⟩
     suc x * (y * z)
     ∎
    where open ≡-Reasoning

open import Relation.Binary.PropositionalEquality
  using (_≡_; module ≡-Reasoning) 
  public 

module PropEq where 
  open Relation.Binary.PropositionalEquality 
    using (refl; cong; sym; trans)
    public 

open import Data.Bool 
  using (if_then_else_) 
  public 

open import Function 
  using (case_of_) 
  public 

open import Data.Bool.Properties 
  using (∨-identityˡ; ∨-identityʳ;
         ∨-zeroˡ; ∨-zeroʳ;
         ∨-assoc; ∧-assoc;
         ∧-identityˡ; ∧-identityʳ;
         ∧-zeroˡ; ∧-zeroʳ;
         not-involutive 
        )
  public 

open import Data.Nat.Properties 
  using (+-identityˡ; +-identityʳ;
         *-identityˡ; *-identityʳ;
         *-zeroˡ; *-zeroʳ;
         +-assoc; *-assoc;
         +-comm; *-comm;
         ^-identityʳ;
         +-suc; suc-injective;
         *-distribˡ-+; *-distribʳ-+
        )
  public 