module Chapter6-Decidability where 

open import Chapter1-Agda using (Bool; true; false) 
open import Chapter2-Numbers using (ℕ; zero; suc; _+_)
open import Chapter3-Proofs using (_≡_; module PropEq; module ≡-Reasoning; suc-injective) 
open PropEq 
open import Chapter4-Relations using (Level; _⊔_; lsuc; Σ; _,_) 

module Sandbox-Inequality where 
  data _≢_ {A : Set} : A → A → Set where 
    ineq : {x y : A} → x ≢ y 

  f : ℕ → ℕ → ℕ 
  f x y = x + y 
  
module Sandbox-Explosion where 
  _IsFalse : Set → Set₁ 
  P IsFalse = P → {A : Set} → A 

  2≢3 : (2 ≡ 3) IsFalse 
  2≢3 ()


module Definition-Bottom where 
  data ⊥ : Set where 
  
  2≢3 : 2 ≡ 3 → ⊥ 
  2≢3 ()

  ⊥-elim : {A : Set} → ⊥ → A 
  ⊥-elim ()

  ⊥-unique : {x y : ⊥} → x ≡ y 
  ⊥-unique {x} = ⊥-elim x

  ¬_ : {ℓ : Level} → Set ℓ → Set ℓ 
  ¬ P = P → ⊥ 
  infix 3 ¬_

  _≢_ : {A : Set} → A → A → Set 
  x ≢ y = ¬ x ≡ y 
  infix 4 _≢_

  ≢-sym : {A : Set} {x y : A} → x ≢ y → y ≢ x 
  ≢-sym x≢y y=x = x≢y (sym y=x)

  Reflexive : {c ℓ : Level} {A : Set c} → (A → A → Set ℓ) → Set (ℓ ⊔ c) 
  Reflexive {A = A} _≈_ = {x : A} → x ≈ x 

  ≡-refl : {A : Set} → Reflexive {A = A} _≡_ 
  ≡-refl = refl 

  ¬≢-refl : ¬ ({A : Set} → Reflexive {A = A} _≢_) 
  ¬≢-refl x = x {ℕ} {0} refl 

  -- Not Possible! 
  --¬≢-refl-bad : {A : Set} → ¬ Reflexive {A = A} _≢_ 
  --¬≢-refl-bad x = x {!   !} refl

  -- Compare good to bad 
  -- ¬≢-refl : ({A : Set} → {x : A} → x ≡ x → ⊥) → ⊥ 
  -- the implementer (the user) gets to pick A 
  -- vs 
  -- ¬≢-refl-bad : {A : Set} → ({x : A} → x ≡ x → ⊥) → ⊥ 
  -- the caller (the proof checker) gets to pick A, what if they pick a bad one?

  Transitive : {c ℓ : Level} {A : Set c} → (A → A → Set ℓ) → Set (c ⊔ ℓ) 
  Transitive {A = A} _≈_ = {x y z : A} → x ≈ y → y ≈ z → x ≈ z

  ¬≢-trans : ¬ ({A : Set} → Transitive {A = A} _≢_) 
  ¬≢-trans ≢-trans = ≢-trans {ℕ} 2≢3 (≢-sym 2≢3) refl

open import Relation.Nullary using (¬_) 

module Example-NoMonusLeftIdentity where 
  open Chapter2-Numbers using (_∸_) 

  ¬∸-identityˡ : ¬ Σ ℕ (λ e → (x : ℕ) → e ∸ x ≡ x) 
  ¬∸-identityˡ (e , e-is-id)
    with e-is-id 0 | e-is-id 1 
  ... | refl | ()

module Sandbox-Decidability where 
  open Chapter2-Numbers using (Maybe; just; nothing)

  n=5? : (n : ℕ) → Maybe (n ≡ 5) 
  n=5? 5 = just refl 
  n=5? _ = nothing 

  data Dec {ℓ : Level} (P : Set ℓ) : Set ℓ where 
    yes :   P → Dec P 
    no  : ¬ P → Dec P 

open import Relation.Nullary using (Dec; yes; no) 
 
module Nat-Properties where 
  _==_ : ℕ → ℕ → Bool 
  zero == zero = true
  zero == suc y = false
  suc x == zero = false
  suc x == suc y = x == y 

  _≟_ : (x y : ℕ) → Dec (x ≡ y) 
  zero ≟ zero = yes refl
  zero ≟ suc y = no λ ()
  suc x ≟ zero = no λ ()
  suc x ≟ suc y with x ≟ y 
  ... | yes refl = yes refl 
  ... | no x≢y   = no λ { refl → x≢y refl }

  DecidableEquality : {ℓ : Level} (A : Set ℓ) → Set ℓ 
  DecidableEquality A = (x y : A) → Dec (x ≡ y)

  _≟ℕ_ : DecidableEquality ℕ 
  _≟ℕ_ = _≟_ 

  map-dec : {ℓ₁ ℓ₂ : Level} {P : Set ℓ₁} {Q : Set ℓ₂} → 
            (P → Q) → (Q → P) → 
            Dec P → Dec Q 
  map-dec to from (yes p) = yes (to p)
  map-dec to from (no ¬p) = no (λ q → ¬p (from q))

open import Relation.Binary using (DecidableEquality) 

module BinaryTrees where 
  
  data BinTree {ℓ : Level} (A : Set ℓ) : Set ℓ where 
    empty  : BinTree A 
    branch : BinTree A → A → BinTree A → BinTree A 

  {-
  tree : BinTree ℕ 
  tree = 
    branch 
      (branch (branch empty 0 empty) 0 (branch empty 2 empty)) 
      4
      (branch empty 6 empty) 
  -}

  pattern leaf a = branch empty a empty 

  is-singleton : {A : Set} → BinTree A → Bool 
  is-singleton (leaf _) = true 
  is-singleton _       = false 

  five-tree : BinTree ℕ 
  five-tree = leaf 5

  tree : BinTree ℕ 
  tree = branch (branch (leaf 0) 0 (leaf 2)) 4 (leaf 6)

  {- 
  data _∈_ {ℓ : Level} {A : Set ℓ} : A → BinTree A → Set ℓ where 
    here  : {a : A} {l r : BinTree A} → a ∈ branch l a r 
    left  : {a b : A} {l r : BinTree A} → a ∈ l → a ∈ branch l b r 
    right : {a b : A} {l r : BinTree A} → a ∈ r → a ∈ branch l b r 
  -}

  private variable 
    ℓ : Level 
    A : Set ℓ 
    a b : A 
    l r : BinTree A 

  -- the test does not have the implicit argument, but there must have been a version change
  -- the file does not typecheck unless we add back the implicit argument for A or 
  -- we add the large indices flag
  data _∈_ {A : Set ℓ} : A → BinTree A → Set ℓ where 
    here  : a ∈ branch l a r 
    left  : a ∈ l → a ∈ branch l b r 
    right : a ∈ r → a ∈ branch l b r 

  6∈tree : 6 ∈ tree 
  6∈tree = right here

  Decidable : {c ℓ : Level} {A : Set c} 
              → (A → Set ℓ) → Set (c ⊔ ℓ) 
  Decidable {A = A} P = (a : A) → Dec (P a)

  Decidable₂ : {c ℓ : Level} {A : Set c} 
               → (A → A → Set ℓ) → Set (c ⊔ ℓ) 
  Decidable₂ {A = A} _~_ = (x y : A) → Dec (x ~ y) 

  ∈? : DecidableEquality A → (t : BinTree A) → Decidable (_∈ t) 
  ∈? _≟_ empty a = no λ ()
  ∈? _≟_ (branch l x r) a 
    with x ≟ a   | ∈? _≟_ l a 
  ... | yes refl | _    = yes here 
  ... | no _     | yes x∈l = yes (left x∈l)
  ... | no x≢a   | no  x∉l with ∈? _≟_ r a
  ... | yes x∈r = yes (right x∈r)
  ... | no  x∉r =
    no λ { here      → x≢a refl
         ; (left p)  → x∉l p
         ; (right p) → x∉r p
         }

  open Nat-Properties using (_≟ℕ_) 

  _ : ∈? _≟ℕ_ tree 2 ≡ yes _ 
  _ = refl 

  _ : ∈? _≟ℕ_ tree 7 ≡ no _ 
  _ = refl 

  data All {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (P : A → Set ℓ₂) : BinTree A → Set (ℓ₁ ⊔ ℓ₂) where 
    empty  : All P empty 
    branch : All P l → P a → All P r → All P (branch l a r)

  pattern leaf a = branch empty a empty 

  open Chapter2-Numbers using (IsEven; z-even; ss-even) 

  tree-all-even : All IsEven tree 
  tree-all-even = branch
    (branch (leaf z-even) z-even
     (leaf (ss-even z-even)))
    (ss-even (ss-even z-even))
    (leaf (ss-even (ss-even (ss-even z-even))))

  all? : {P : A → Set} → Decidable P → Decidable (All P) 
  all? p? empty = yes empty
  all? p? (branch l a r) with p? a | all? p? l | all? p? r 
  ... | no ¬pa | _      | _      = no λ { (branch _ pa _) → ¬pa pa } 
  ... | yes _  | no ¬al | _      = no λ { (branch al _ _) → ¬al al }
  ... | yes _  | yes _  | no ¬ar = no λ { (branch _ _ ar) → ¬ar ar }
  ... | yes pa | yes al | yes ar = yes (branch al pa ar)

  data IsBST {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (_<_ : A → A → Set ℓ₂) : BinTree A → Set (ℓ₁ ⊔ ℓ₂) where 
    bst-empty : IsBST _<_ empty 
    bst-branch : All (_< a) l → All (a <_) r → IsBST _<_ l → IsBST _<_ r → IsBST _<_ (branch l a r) 

  open Chapter4-Relations using (_≤_; z≤n; s≤s; _<_) 

  tree-is-bst : IsBST _≤_ tree 
  tree-is-bst = bst-branch
    (branch (branch empty z≤n empty) z≤n
     (branch empty (s≤s (s≤s z≤n)) empty))
    (branch empty (s≤s (s≤s (s≤s (s≤s z≤n)))) empty)
    (bst-branch (branch empty z≤n empty) (branch empty z≤n empty)
     (bst-branch empty empty bst-empty bst-empty)
     (bst-branch empty empty bst-empty bst-empty))
    (bst-branch empty empty bst-empty bst-empty)

  is-bst? : {_≤_ : A → A → Set} → Decidable₂ _≤_ → Decidable (IsBST _≤_) 
  is-bst? _≤?_ empty = yes bst-empty
  is-bst? _≤?_ (branch l a r) = {!   !}

  -- stopped page 244 at the end of Section 6.13 

