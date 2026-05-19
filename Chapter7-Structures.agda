module Chapter7-Structures where 

open import Chapter1-Agda
open import Chapter2-Numbers 
open import Chapter3-Proofs renaming (module PropEq to ≡)
open import Chapter4-Relations
open import Chapter5-Modular-Arithmetic
    using (equiv-to-preorder; ≡-is-equivalence; refl; sym; trans)
open import Chapter6-Decidability using (¬_; ⊥) 
open Chapter6-Decidability.BinaryTrees using (BinTree; leaf; branch; empty)

private variable 
  ℓ ℓ₁ ℓ₂ : Level 
  A : Set ℓ 
  B : Set ℓ 
  C : Set ℓ 

private 
  Op₂ : {ℓ : Level} → Set ℓ → Set ℓ 
  Op₂ A = A → A → A 

module Sandbox-Naive-Monoids where 
  
  record IsMonoid {Carrier : Set ℓ} 
                  (_·_ : Op₂ Carrier) 
                  (ε : Carrier) 
    : Set (lsuc ℓ) where 
    field 
      assoc : (x y z : Carrier) → (x · y) · z ≡ x · (y · z) 
      identityˡ : (x : Carrier) → ε · x ≡ x 
      identityʳ : (x : Carrier) → x · ε ≡ x 

  open IsMonoid 

  *-1 : IsMonoid _*_ 1 
  assoc *-1 = *-assoc 
  identityˡ *-1 = *-identityˡ 
  identityʳ *-1 = *-identityʳ 

  +-0 : IsMonoid _+_ 0 
  assoc +-0 = +-assoc 
  identityˡ +-0 = +-identityˡ 
  identityʳ +-0 = +-identityʳ  

  ∨-false : IsMonoid _∨_ false 
  assoc ∨-false = ∨-assoc 
  identityˡ ∨-false = ∨-identityˡ
  identityʳ ∨-false = ∨-identityʳ 

  ∧-true : IsMonoid _∧_ true 
  assoc ∧-true = ∧-assoc 
  identityˡ ∧-true = ∧-identityˡ 
  identityʳ ∧-true = ∧-identityʳ

  xor : Bool → Bool → Bool 
  xor false y = y
  xor true y = not y

  xor-assoc : (x y z : Bool) → xor (xor x y) z ≡ xor x (xor y z) 
  xor-assoc false y z = refl
  xor-assoc true false z = refl
  xor-assoc true true false = refl
  xor-assoc true true true = refl

  xor-identityˡ : (x : Bool) → xor false x ≡ x 
  xor-identityˡ x = refl

  xor-identityʳ : (x : Bool) → xor x false ≡ x 
  xor-identityʳ false = refl
  xor-identityʳ true = refl

  xor-false : IsMonoid xor false 
  xor-false .assoc = xor-assoc 
  xor-false .identityˡ = xor-identityˡ
  xor-false .identityʳ = xor-identityʳ 

  record Monoid {c : Level} (Carrier : Set c) : Set (lsuc c) where 
    infixl 7 _·_ 
    field 
      _·_ : Op₂ Carrier 
      ε   : Carrier 
      is-monoid : IsMonoid _·_ ε 
  
  bundle : {c : Level} {A : Set c} { · : Op₂ A} {ε : A} → IsMonoid · ε → Monoid A 
  Monoid._·_ (bundle {· = ·} x) = · 
  Monoid.ε (bundle {ε = ε} x) = ε 
  Monoid.is-monoid (bundle x) = x 

  open Monoid ⦃ ... ⦄ 

  module _ ⦃ _ : Monoid Bool ⦄ where 
    ex₁ : Bool 
    ex₁ = false · true · false · false 

    ex₂ : Bool 
    ex₂ = true · true · true · true 

    ex₃ : Bool 
    ex₃ = ε 

  
  {- "The way to think about ex₁ and friends is that they compute abstract summaries of the booleans 
      multiplied together in each. By instantiating them with different Monoids, we can get different 
      summaries of the data. For example, if we were to use bundle ∨-false, we could compute if there 
      exists at least one true in each data set." -page 254 -}

  module _ where 
    private instance 
      _ = bundle ∨-false 
    
    _ : ex₁ ≡ true 
    _ = refl 

    _ : ex₂ ≡ true 
    _ = refl 

    _ : ex₃ ≡ false 
    _ = refl 

  {- "Alternatively, if we were to use bundle ∧-true, we would instead 
      compute whether every boolean in the dataset be true:"-}

  module _ where 
    private instance 
      _ = bundle ∧-true 

    _ : ex₁ ≡ false  
    _ = refl

    _ : ex₂ ≡ true 
    _ = refl 

    _ : ex₃ ≡ true 
    _ = refl 

  {- "As a third illustration of summarizing this dataset, we can use the xor-false monoid 
     to determine whether there is an odd number of trues in each example."-}

  module _ where 
    private instance 
      _ = bundle xor-false 

    _ : ex₁ ≡ true 
    _ = refl 

    _ : ex₂ ≡ false  
    _ = refl 

    _ : ex₃ ≡ false 
    _ = refl 

  _<∣>_ : Maybe A → Maybe A → Maybe A 
  just x <∣> my = just x
  nothing <∣> my = my

  <∣>-assoc : (mx my mz : Maybe A) → (mx <∣> my) <∣> mz ≡ mx <∣> (my <∣> mz)
  <∣>-assoc (just x) my mz = refl
  <∣>-assoc nothing my mz = refl

  <∣>-identityˡ : (mx : Maybe A) → nothing <∣> mx ≡ mx 
  <∣>-identityˡ mx = refl

  <∣>-identityʳ : (mx : Maybe A) → mx <∣> nothing ≡ mx 
  <∣>-identityʳ (just x) = refl
  <∣>-identityʳ nothing = refl

  <∣>-nothing : IsMonoid {Carrier = Maybe A} _<∣>_ nothing
  <∣>-nothing .assoc = <∣>-assoc
  <∣>-nothing .identityˡ = <∣>-identityˡ
  <∣>-nothing .identityʳ = <∣>-identityʳ 

  flip : (A → B → C) → B → A → C 
  flip f b a = f a b 

  dual : {_·_ : Op₂ A} {ε : A} → IsMonoid _·_ ε → IsMonoid (flip _·_) ε 
  dual m .assoc x y z = sym (assoc m z y x)
  dual m .identityˡ = identityʳ m
  dual m .identityʳ = identityˡ m 

  module Definition-List where 
    data List (A : Set ℓ) : Set ℓ where 
      [] : List A 
      _∷_ : A → List A → List A 
    infixr 5 _∷_ 
  
    _++_ : List A → List A → List A 
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  open import Data.List using (List; []; _∷_; _++_) 

  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs) 
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl 

  ++-identityˡ : (xs : List A) → [] ++ xs ≡ xs 
  ++-identityˡ xs = refl

  ++-identityʳ : (xs : List A) → xs ++ [] ≡ xs 
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl
  
  ++-[] : IsMonoid {Carrier = List A} _++_ [] 
  ++-[] .assoc = ++-assoc
  ++-[] .identityˡ = ++-identityˡ
  ++-[] .identityʳ = ++-identityʳ

  _∘_ : (B → C) → (A → B) → (A → C) 
  (g ∘ f) x = g (f x)

  id : A → A 
  id a = a 

  ∘-id : IsMonoid {Carrier = A → A} _∘_ id 
  ∘-id .assoc x y z = refl
  ∘-id .identityˡ x = refl
  ∘-id .identityʳ x = refl

  module ListSummaries where 
    foldList : ⦃ Monoid B ⦄ → (A → B) → List A → B 
    foldList f [] = ε
    foldList f (x ∷ xs) = f x · foldList f xs 

    any? : (A → Bool) → List A → Bool 
    any? = foldList ⦃ bundle ∨-false ⦄ 

    all? : (A → Bool) → List A → Bool 
    all? = foldList ⦃ bundle ∧-true ⦄ 

    sum : List ℕ → ℕ 
    sum = foldList ⦃ bundle +-0 ⦄ id 

    _ : sum (1 ∷ 20 ∷ 300 ∷ []) ≡ 321 
    _ = refl 

    product : List ℕ → ℕ 
    product = foldList ⦃ bundle *-1 ⦄ id 

    flatten : List (List A) → List A 
    flatten = foldList ⦃ bundle ++-[] ⦄ id 

    head : List A → Maybe A 
    head = foldList ⦃ bundle <∣>-nothing ⦄ just 

    foot : List A → Maybe A 
    foot = foldList ⦃ bundle (dual <∣>-nothing) ⦄ just 

    reverse : List A → List A 
    reverse = foldList ⦃ bundle (dual ++-[]) ⦄ (_∷ [])  

    const : A → B → A 
    const a _ = a  

    size : List A → ℕ 
    size = foldList ⦃ bundle +-0 ⦄ (const 1) 

    empty? : List A → Bool 
    empty? = foldList ⦃ bundle ∧-true ⦄ (const false) 

  open import Function using (id; const) 

  record Foldable {ℓ₁ ℓ₂ : Level} (Container : Set ℓ₁ → Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where 
    field 
      fold : {B : Set ℓ₂} → ⦃ monoid : Monoid B ⦄ → (A → B) → Container A → B 
  
  open Foldable ⦃ ... ⦄ 

  instance 
    fold-list : Foldable {ℓ} List 
    Foldable.fold fold-list = ListSummaries.foldList 

    fold-bintree : Foldable {ℓ} BinTree 
    fold-bintree .Foldable.fold f empty = ε
    fold-bintree .Foldable.fold f (branch l a r) = Foldable.fold fold-bintree f l · f a · Foldable.fold fold-bintree f r

    fold-maybe : Foldable {ℓ} Maybe 
    fold-maybe .Foldable.fold f (just x) = f x
    fold-maybe .Foldable.fold f nothing = ε 

  size : {A : Set ℓ} {Container : Set ℓ → Set} → ⦃ Foldable Container ⦄ → Container A → ℕ 
  size = fold ⦃ monoid = bundle +-0 ⦄ (const 1) 

  _ : size (1 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ 4 
  _ = refl 

  _ : size (branch (leaf true) false (leaf true)) ≡ 3 
  _ = refl 

  toList : ∀ {Container} → ⦃ Foldable Container ⦄ → Container A → List A 
  toList = fold ⦃ monoid = bundle ++-[] ⦄ (_∷ []) 

  --stopping at Sectino 7.7 on page 275
 