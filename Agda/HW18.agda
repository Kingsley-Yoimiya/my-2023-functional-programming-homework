module HW18 where

-- How to type those Unicode characters:
-- →   \->
-- ≡   \==
-- ≢   \==n
-- ⟨   \<
-- ⟩   \>
-- ∎   \qed
-- ∘   \o
-- ∷   \::
-- ℕ   \bN
-- ⊕   \oplus
-- ˡ   \^l       (4th candidate, use your right arrow key to select)
-- ʳ   \^r       (4th candidate, use your right arrow key to select)
-- ₁   \_1
-- ×   \x
-- ∀   \all
-- Σ   \Sigma
-- ∃   \ex
-- ⊆   \subseteq
-- ≤   \le
-- ⊔   \sqcup
-- ¬   \neg
-- ⊥   \bot
-- ∈   \in

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong-app; subst; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function using (id; _∘_)

module problem-1 where

  open import Data.List using (List; []; _∷_; _++_)

  ++-assoc : ∀ {A : Set}
      (xs ys zs : List A)
      -----------------------------------
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

  -- tips: to input the superscript l (ˡ), type \^l and use your
  --       arrow keys to select it (should be the fourth candidate).
  ++-identityˡ : ∀ {A : Set}
      (xs : List A)
      -------------
    → [] ++ xs ≡ xs
  ++-identityˡ [] = refl
  ++-identityˡ (x ∷ xs) rewrite ++-identityˡ xs = refl  

  -- you might have already guessed it: type \^r for superscript r (ʳ)
  -- again, use your arrow keys to select it (the fourth candidate). 
  ++-identityʳ : ∀ {A : Set}
      (xs : List A)
    → xs ++ [] ≡ xs
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl  

module problem-2 where

  open import Data.List using (List; []; _∷_; _++_; foldr)

  -- tips: to input ⊗, type \otimes
  foldr-++ : ∀ {A : Set}
      (_⊗_ : A → A → A)
      (e : A)
      (xs ys : List A)
      -----------------------------
    → foldr _⊗_ e (xs ++ ys)
    ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
  foldr-++ f e [] ys rewrite problem-1.++-identityˡ ys = refl
  foldr-++ f e (x ∷ xs) ys rewrite foldr-++ f e xs ys = refl

    
module problem-3 (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where

  open import Data.List using (List; []; _∷_; _++_; head)

  reverse : ∀ {A : Set} → List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

  -- hint: you might want to introduce an extra lemma to prove this.

  get-reverse : ∀ {A : Set} → (x y : List A) → reverse (x ++ y) ≡ reverse y ++ reverse x
  --get-reverse xs [] rewrite problem-1.++-identityʳ xs = refl
  --get-reverse xs (y ∷ ys) rewrite get-reverse xs ys = {!!}
  get-reverse [] ys rewrite problem-1.++-identityˡ ys | problem-1.++-identityʳ (reverse ys) = refl
  get-reverse (x ∷ xs) ys rewrite get-reverse xs ys | problem-1.++-assoc (reverse ys) (reverse xs) (x ∷ []) = refl

  
  
  reverse-involutive : ∀ {A : Set} → reverse {A} ∘ reverse {A} ≡ id
  reverse-involutive = extensionality reverse-invol-x
    where
      reverse-invol-x : ∀ {A : Set} → (x : List A) → (reverse {A} ∘ reverse {A}) (x) ≡ x
      reverse-invol-x [] = refl
      reverse-invol-x (x ∷ xs) rewrite get-reverse xs (x ∷ []) | get-reverse (reverse xs) (x ∷ []) | reverse-invol-x xs = refl

  -- bonus: fast-reverse-involutive
  -- this is only for practice, not part of the homework this week

  -- fast-reverse : ∀ {A : Set} → List A → List A
  -- fast-reverse = helper []
  --   module FastReverse where
  --   helper : ∀ {A : Set} → List A → List A → List A
  --   helper res []       = res
  --   helper res (x ∷ xs) = helper (x ∷ res) xs

  -- fast-reverse-involutive : ∀ {A : Set}
  --   → fast-reverse {A} ∘ fast-reverse {A} ≡ id
  -- fast-reverse-involutive = ?

module semigroup where
  record IsSemigroup {A : Set} (_⊕_ : A → A → A) : Set where
    field assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)

  open IsSemigroup public

  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-assoc)
  ℕ-add-is-semigroup : IsSemigroup _+_
  ℕ-add-is-semigroup .assoc = +-assoc

  open import Data.Nat using (_⊔_)
  open import Data.Nat.Properties using (⊔-assoc)
  ℕ-⊔-is-semigroup : IsSemigroup _⊔_
  ℕ-⊔-is-semigroup .assoc = ⊔-assoc

  open import Data.List using (List; _++_; [])
  open import Data.List.Properties using (++-assoc)
  List-++-is-semigroup : ∀ {A : Set} → IsSemigroup {List A} _++_
  List-++-is-semigroup .assoc = ++-assoc

open semigroup

module monoid where
  record IsMonoid {A : Set} (e : A) (_⊕_ : A → A → A) : Set where
    field
      is-semigroup : IsSemigroup _⊕_
      identityˡ : ∀ x → e ⊕ x ≡ x
      identityʳ : ∀ x → x ⊕ e ≡ x

  open IsMonoid public

  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-identityˡ; +-identityʳ)
  ℕ-add-is-monoid : IsMonoid 0 _+_
  ℕ-add-is-monoid .is-semigroup = ℕ-add-is-semigroup
  ℕ-add-is-monoid .identityˡ = +-identityˡ
  ℕ-add-is-monoid .identityʳ = +-identityʳ

  open import Data.Nat using (_⊔_)
  open import Data.Nat.Properties using (⊔-identityˡ; ⊔-identityʳ)
  ℕ-⊔-is-monoid : IsMonoid 0 _⊔_
  ℕ-⊔-is-monoid .is-semigroup = ℕ-⊔-is-semigroup
  ℕ-⊔-is-monoid .identityˡ = ⊔-identityˡ
  ℕ-⊔-is-monoid .identityʳ = ⊔-identityʳ

  open import Data.List using (List; _++_; [])
  open import Data.List.Properties using (++-identityˡ; ++-identityʳ)
  List-++-is-monoid : ∀ {A : Set} → IsMonoid {List A} [] _++_
  List-++-is-monoid .is-semigroup = List-++-is-semigroup
  List-++-is-monoid .identityˡ = ++-identityˡ
  List-++-is-monoid .identityʳ = ++-identityʳ

open monoid

module MSS (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where
  
  
  open import Data.Nat using (ℕ; _+_; zero; suc; _⊔_)
  open import Data.List using (List; []; _∷_; [_]; _++_; foldl; foldr; map; scanl; scanr; head)

  foldr-monoid : ∀ {A : Set}
                 (_⊗_ : A → A → A)
                 (e : A)
                 → IsMonoid e _⊗_
                 → ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
  foldr-monoid _⊗_ e ⊗-monoid [] y =
    begin
      foldr _⊗_ y []
    ≡⟨⟩
      y
    ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
      (e ⊗ y)
    ≡⟨⟩
      foldr _⊗_ e [] ⊗ y
    ∎
  foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
    begin
      foldr _⊗_ y (x ∷ xs)
    ≡⟨⟩
      x ⊗ (foldr _⊗_ y xs)
    ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
      x ⊗ (foldr _⊗_ e xs ⊗ y)
    ≡⟨ sym(assoc (IsMonoid.is-semigroup ⊗-monoid) x (foldr _⊗_ e xs) y) ⟩
      (x ⊗ foldr _⊗_ e xs) ⊗ y
    ∎
  
  foldr-monoid-++ : ∀ {A : Set}
                    (_⊗_ : A → A → A)
                    (e : A)
                    → IsMonoid e _⊗_
                    → ∀ (xs ys : List A)
                    → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
    begin
      foldr _⊗_ e (xs ++ ys)
    ≡⟨ problem-2.foldr-++ _⊗_ e xs ys ⟩
      foldr _⊗_ (foldr _⊗_ e ys) xs
    ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
      foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
    ∎
  
  map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) → (map g ∘ map f) ≡ map (g ∘ f)
  map-compose f g = extensionality (map-compose-p f g) where
    map-compose-p : ∀ {A B C : Set} (f : A → B) (g : B → C) (x : List A) → (map g ∘ map f) x ≡ map (g ∘ f) x
    
    map-compose-p f g [] = refl
      
    map-compose-p f g (x ∷ xs) =
      begin
        (map g ∘ map f) (x ∷ xs)
      ≡⟨⟩
        map g (map f (x ∷ xs))
      ≡⟨⟩
        map g (f x ∷ (map f xs))
      ≡⟨⟩
        g (f x) ∷ map g (map f xs)
      ≡⟨ cong (g (f x) ∷_) (map-compose-p f g xs) ⟩
        g (f x) ∷ map (g ∘ f) xs
      ≡⟨⟩
        (g ∘ f) x ∷ map (g ∘ f) xs
      ∎

  reduce-promotion : ∀ {A : Set}
                     (_⊕_ : A → A → A)
                     (e : A)
                     (p : IsMonoid e _⊕_)
                     → foldr _⊕_ e ∘ foldr _++_ [] ≡ foldr _⊕_ e ∘ map (foldr _⊕_ e)
  reduce-promotion _⊕_ e p = extensionality (reduce-promotion-x _⊕_ e p) where
    reduce-promotion-x :
                       ∀ {A : Set}
                       (_⊕_ : A → A → A)
                       (e : A)
                       (p : IsMonoid e _⊕_)
                       (x : List (List A))
                       → (foldr _⊕_ e ∘ foldr _++_ []) x ≡ (foldr _⊕_ e ∘ map (foldr _⊕_ e)) x
    reduce-promotion-x _⊕_ e p [] = refl
    reduce-promotion-x _⊕_ e p (x ∷ xs) =
      begin
        (foldr _⊕_ e ∘ foldr _++_ []) (x ∷ xs)
      ≡⟨⟩
        (foldr _⊕_ e) (foldr _++_ [] (x ∷ xs))
      ≡⟨⟩
        (foldr _⊕_ e) (x ++ (foldr _++_ [] xs))
      ≡⟨ foldr-monoid-++ _⊕_ e p x (foldr _++_ [] xs) ⟩
        (foldr _⊕_ e x) ⊕ foldr _⊕_ e (foldr _++_ [] xs)
      ≡⟨ cong(foldr _⊕_ e x ⊕_) (reduce-promotion-x _⊕_ e p xs) ⟩
        (foldr _⊕_ e x) ⊕ foldr _⊕_ e (map (foldr _⊕_ e) xs)
      ≡⟨ refl ⟩
        (foldr _⊕_ e ((foldr _⊕_ e x) ∷ (map (foldr _⊕_ e) xs)))
      ≡⟨⟩
        (foldr _⊕_ e ∘ map (foldr _⊕_ e)) (x ∷ xs)
      ∎
  
  R-Dist : ∀ {A : Set}
             (_⊕_ : A → A → A)
             (_⊗_ : A → A → A)
           → Set
  R-Dist {A} _⊕_ _⊗_ = ∀ (z x y : A) → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)

-- ∀ (a b c : A) → (a ⊕ b) ⊗ c ≡ (a ⊗ c) ⊕ (b ⊗ c)
  
  inits : ∀ {A : Set} → List A → List (List A)
  inits [] = [ [] ]
  inits (x ∷ xs) = [] ∷ (map (x ∷_) (inits xs))
  -- inits = scanl _++_ [] ∘ map [_]

  tails : ∀ {A : Set} → List A → List (List A)
  tails [] = [ [] ] 
  tails (x ∷ xs) = [ x ∷ xs ] ++ tails xs 
  -- scanr _++_ [] ∘ map [_]
  -- the defination of tails is a smart but stupid in proof.

  concat : ∀ {A : Set} → List (List A) → List A
  concat = foldr _++_ []

  segs : ∀ {A : Set} → List A → List (List A)
  segs = concat ∘ map tails ∘ inits

  sum : List ℕ → ℕ
  sum = foldr _+_ 0

  maximum : List ℕ → ℕ
  maximum = foldr _⊔_ 0

  -- Did you know there are plenty of useful theorems in the standard library?
  open import Data.Nat.Properties using (+-distribˡ-⊔; +-distribʳ-⊔)
  -- +-distribˡ-⊔ : ∀ x y z → x + (y ⊔ z) ≡ (x + y) ⊔ (x + z)
  -- +-distribʳ-⊔ : ∀ z x y → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
  
  map-promotion : ∀{A B : Set} (f : A → B) 
    → (map f) ∘ concat ≡ concat ∘ (map (map f))
  map-promotion = {!!}
  
  horner-rule : ∀{A : Set}
                (_⊕_ : A → A → A)
                (e-⊕ : A)
                (_⊗_ : A → A → A)
                (e-⊗ : A)
              → (p : IsMonoid e-⊕ _⊕_)
              → (q : IsMonoid e-⊗ _⊗_)
              → (rdist : R-Dist _⊕_ _⊗_)
              → foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗) ∘ tails
                ≡ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗
  l-trans-rule : ∀ {A : Set}
                   (_⊕_ : A → A → A)
                   (e-⊕ : A)
                   (_⊗_ : A → A → A)
                   (e-⊗ : A)
                 → (p : IsMonoid e-⊕ _⊕_)
                 → (q : IsMonoid e-⊗ _⊗_)
                 → (rdist : R-Dist _⊕_ _⊗_)
                 → (t : A)
                 → (xs : List A)
                 → foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (t ⊕ e-⊗) xs ≡
                   (foldr _⊗_ e-⊗ (t ∷ xs)) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
  l-trans-rule _⊕_ e-⊕ _⊗_ e-⊗ p q rdist t [] =
    begin
      t ⊕ e-⊗
    ≡⟨ cong (_⊕ e-⊗) (sym(identityʳ q t)) ⟩
      (t ⊗ e-⊗) ⊕ e-⊗
    ≡⟨⟩
      (foldr _⊗_ e-⊗ (t ∷ [])) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ []
    ∎
  l-trans-rule {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist t (x ∷ xs) =
    begin
      foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (t ⊕ e-⊗) (x ∷ xs)
    ≡⟨⟩
      foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (((t ⊕ e-⊗) ⊗ x) ⊕ e-⊗) xs
    ≡⟨ cong (λ yy → foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (yy ⊕ e-⊗) xs) (rdist x t e-⊗) ⟩
      foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (((t ⊗ x) ⊕ (e-⊗ ⊗ x)) ⊕ e-⊗) xs
    ≡⟨ l-trans-rule _⊕_ e-⊕ _⊗_ e-⊗ p q rdist ((t ⊗ x) ⊕ (e-⊗ ⊗ x)) xs ⟩
      foldr _⊗_ e-⊗ (((t ⊗ x) ⊕ (e-⊗ ⊗ x)) ∷ xs) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨ cong (λ yy → (foldr _⊗_ e-⊗ (yy ∷ xs) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs))) (sym(rdist x t e-⊗)) ⟩
      foldr _⊗_ e-⊗ (((t ⊕ e-⊗) ⊗ x) ∷ xs) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨⟩
      (((t ⊕ e-⊗) ⊗ x) ⊗ foldr _⊗_ e-⊗ (xs)) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨ cong (λ yy → ((yy) ⊗ foldr _⊗_ e-⊗ (xs)) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)) (rdist x t e-⊗) ⟩
      (((t ⊗ x) ⊕ (e-⊗ ⊗ x)) ⊗ foldr _⊗_ e-⊗ (xs)) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨ cong (λ yy → ((((t ⊗ x) ⊕ yy) ⊗ foldr _⊗_ e-⊗ (xs)) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs))) (identityˡ q x)⟩
      (((t ⊗ x) ⊕ x) ⊗ foldr _⊗_ e-⊗ (xs)) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨ cong(_⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs))(rdist (foldr _⊗_ e-⊗ (xs)) (t ⊗ x) x)⟩
      (((t ⊗ x) ⊗ foldr _⊗_ e-⊗ (xs)) ⊕ (x ⊗ foldr _⊗_ e-⊗ (xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨ cong (λ yy → (yy ⊕ (x ⊗ foldr _⊗_ e-⊗ (xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)) (assoc (IsMonoid.is-semigroup q)  t x (foldr _⊗_ e-⊗ (xs))) ⟩
      ((t ⊗ (x ⊗ foldr _⊗_ e-⊗ (xs))) ⊕ (x ⊗ foldr _⊗_ e-⊗ (xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨⟩
      ((t ⊗ (foldr _⊗_ e-⊗ ((x ∷ xs)))) ⊕ (x ⊗ foldr _⊗_ e-⊗ (xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ≡⟨⟩
      (((foldr _⊗_ e-⊗ ((t ∷ x ∷ xs)))) ⊕ (foldr _⊗_ e-⊗ (x ∷ xs)))
      ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
    ------
    ≡⟨ assoc (is-semigroup p) (t ⊗ (x ⊗ foldr _⊗_ e-⊗ xs))
         (x ⊗ foldr _⊗_ e-⊗ xs) (foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) e-⊗ xs) ⟩
      ((foldr _⊗_ e-⊗ ((t ∷ x ∷ xs)))) ⊕ ((foldr _⊗_ e-⊗ (x ∷ xs))
      ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs))
    ≡⟨ refl ⟩
      ((foldr _⊗_ e-⊗ ((t ∷ x ∷ xs)))) ⊕ ((foldr _⊗_ e-⊗ (x ∷ xs))
      ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs))
    ≡⟨ cong(((foldr _⊗_ e-⊗ ((t ∷ x ∷ xs)))) ⊕_) (sym(l-trans-rule _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x xs))⟩
      (foldr _⊗_ e-⊗ (t ∷ (x ∷ xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (x ⊕ e-⊗) (xs)
    ≡⟨ cong(λ yy → (foldr _⊗_ e-⊗ (t ∷ (x ∷ xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (yy ⊕ e-⊗) (xs)) (sym(identityˡ q x)) ⟩
      (foldr _⊗_ e-⊗ (t ∷ (x ∷ xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) ((e-⊗ ⊗ x) ⊕ e-⊗) (xs)
    ≡⟨⟩
      (foldr _⊗_ e-⊗ (t ∷ (x ∷ xs))) ⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (x ∷ xs)
    ∎
  {-
  tails-rule : ∀{A : Set}
               (t : A)
               (xs : List A)
             → tails (t ∷ xs) ≡ [ t ∷ xs ] ++ tails(xs)
  tails-rule t [] = refl
  tails-rule t (x ∷ xs) = extensionality(tails-rule-x t x xs) where
    tails-rule-x : ∀{A : Set}
                    (t : A)
                    (x : A)
                    (xs : List A)
                  → tails (t ∷ x ∷ xs) ≡ [ t ∷ x ∷ xs ] ++ tails(x ∷ xs)
    tails-rule-x t x [] =
      begin
        tails (t ∷ x ∷ [])
      ≡⟨⟩
        tails (t ∷ [ x ])
      ≡⟨⟩
        [ t ∷ [ x ] ] ++ tails [ x ]
      ≡⟨⟩
        [ t ∷ x ∷ [] ] ++ tails [ x ]
      ≡⟨⟩
        [ t ∷ x ∷ [] ] ++ tails(x ∷ [])
      ∎
    tails-rule-x t x (y ∷ ys) =
      begin
        tails (t ∷ x ∷ y ∷ ys)
      ≡⟨⟩
        tails (t ∷ (x ∷ y ∷ ys))
      ≡⟨⟩
        [ t ∷ (x ∷ y ∷ ys) ] ++ tails (x ∷ y ∷ ys)
      ≡⟨ cong([ t ∷ _ ] ++_) (tails-rule-x x y ys) ⟩
        [ t ∷ x ∷ y ∷ ys ] ++ tails (y ∷ ys)
      ≡⟨⟩
        [ t ∷ x ∷ y ∷ ys ] ++ tails (y ∷ ys)
      ≡⟨⟩
        [ t ∷ x ∷ y ∷ ys ] ++ tails (x ∷ y ∷ ys)
      ∎
  -}
  {- tails-rule t (x ∷ xs) =
    begin
      (scanr _++_ [] ∘ map [_]) (t ∷ x ∷ xs)
    ≡⟨ refl ⟩
      scanr _++_ [] ([ [ t ] ] ++ ([ [ x ] ] ++ map [_] xs))
    ≡⟨ cong(λ y1 → (scanl _++_ [] ([ [ t ] ] ++ y1)))(tails-rule x xs) ⟩
      ?
    ≡⟨ {!!} ⟩
      [ t ∷ x ∷ xs ] ++ tails(x ∷ xs)
    ∎
  -}  
  horner-rule _⊕_ e-⊕ _⊗_ e-⊗ p q rdist = extensionality(horner-rule-x _⊕_ e-⊕ _⊗_ e-⊗ p q rdist)
    where
      horner-rule-x : ∀{A : Set}
                      (_⊕_ : A → A → A)
                      (e-⊕ : A)
                      (_⊗_ : A → A → A)
                      (e-⊗ : A)
                    → (p : IsMonoid e-⊕ _⊕_)
                    → (q : IsMonoid e-⊗ _⊗_)
                    → (rdist : R-Dist _⊕_ _⊗_)
                    → (xs : List A)
                    → (foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗) ∘ tails) xs
                    ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) xs
      horner-rule-x _⊕_ e-⊕ _⊗_ e-⊗ p q rdist [] =
        begin
          (foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗) ∘ tails) []
        ≡⟨⟩
          foldr _⊕_ e-⊕ (map (foldr _⊗_ e-⊗) [ [] ])
        ≡⟨⟩
          foldr _⊕_ e-⊕ [ e-⊗ ]
        ≡⟨ identityʳ p e-⊗ ⟩
          e-⊗
        ≡⟨⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ []
        ∎
      horner-rule-x _⊕_ e-⊕ _⊗_ e-⊗ p q rdist (x ∷ xs) =
        begin
          (foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗) ∘ tails) (x ∷ xs)
        ≡⟨ refl ⟩
          (foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗)) ([ x ∷ xs ] ++ tails (xs))
        ≡⟨⟩
          foldr _⊕_ e-⊕ ((map (foldr _⊗_ e-⊗)) [ x ∷ xs ] ++
          (map (foldr _⊗_ e-⊗) ∘ tails) (xs))
        ≡⟨ foldr-monoid-++ _⊕_ e-⊕ p ((map (foldr _⊗_ e-⊗)) [ x ∷ xs ]) ((map (foldr _⊗_ e-⊗) ∘ tails) (xs)) ⟩
          foldr _⊕_ e-⊕ (map (foldr _⊗_ e-⊗) [ x ∷ xs ]) ⊕
          foldr _⊕_ e-⊕ ((map (foldr _⊗_ e-⊗) ∘ tails) (xs))
        ≡⟨ cong ((foldr _⊕_ e-⊕ (map (foldr _⊗_ e-⊗) [ x ∷ xs ])) ⊕_)
           (horner-rule-x _⊕_ e-⊕ _⊗_ e-⊗ p q rdist xs) ⟩
        ----------
          foldr _⊕_ e-⊕ (map (foldr _⊗_ e-⊗) [ x ∷ xs ]) ⊕
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
        ≡⟨⟩
          foldr _⊕_ e-⊕ [ foldr _⊗_ e-⊗ (x ∷ xs) ] ⊕
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
        ≡⟨ refl ⟩
          ((foldr _⊗_ e-⊗ (x ∷ xs)) ⊕ e-⊕) ⊕
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
        ≡⟨ cong (_⊕ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs))
           (identityʳ p (foldr _⊗_ e-⊗ (x ∷ xs))) ⟩
          (foldr _⊗_ e-⊗ (x ∷ xs)) ⊕
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (xs)
        ≡⟨ sym(l-trans-rule _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x xs) ⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (x ⊕ e-⊗) xs
        ≡⟨ cong (λ t → foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (t ⊕ e-⊗) xs) (sym(identityˡ q x)) ⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) ((λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ x) xs
        ≡⟨⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ (x ∷ xs)
        ∎

  acc-lemma : ∀ {A : Set}
              (_⊕_ : A → A → A)
              (e : A)
            → scanl _⊕_ e ≡ map (foldl _⊕_ e) ∘ inits
  acc-lemma _⊕_ e = extensionality(acclemma-x _⊕_ e) where
            acclemma-x : ∀ {A : Set}
                         (_⊕_ : A → A → A)
                         (e : A)
                         (xs : List A)
                       → scanl _⊕_ e xs ≡ (map (foldl _⊕_ e) ∘ inits) xs
            acclemma-x _⊕_ e [] = refl
            acclemma-x _⊕_ e (x ∷ xs) =
              begin
                e ∷ scanl _⊕_ (e ⊕ x) xs
              ≡⟨ cong(e ∷_) (acclemma-x _⊕_ (e ⊕ x) xs) ⟩
                e ∷ (map (foldl _⊕_ (e ⊕ x)) ∘ inits) xs
              ≡⟨⟩
                e ∷ map (foldl _⊕_ (e ⊕ x)) (inits xs)
              ≡⟨⟩
                e ∷ map (foldl _⊕_ e ∘ (x ∷_)) (inits xs)
              ≡⟨ cong(λ yy → (e ∷ yy (inits xs))) (sym(map-compose (x ∷_) (foldl _⊕_ e))) ⟩
                e ∷ (map (foldl _⊕_ e) ∘ map (x ∷_)) (inits xs)
              ≡⟨⟩
                e ∷ (map (foldl _⊕_ e) (map (x ∷_) (inits xs)))
              ≡⟨⟩
                map (foldl _⊕_ e) ([] ∷ (map (x ∷_) (inits xs)))
              ≡⟨ refl ⟩
                (map (foldl _⊕_ e) ∘ inits) (x ∷ xs)
              ∎
    
  mss : List ℕ → ℕ
  mss = maximum ∘ map sum ∘ segs

  maxadd : ℕ → ℕ → ℕ
  maxadd x y = (x + y) ⊔ 0
  
  mss-fast : List ℕ → ℕ
  mss-fast = maximum ∘ (scanl maxadd 0)
    
  derivation : mss ≡ mss-fast
  derivation =
    begin
      mss
    ≡⟨⟩
      maximum ∘ map sum ∘ concat ∘ map tails ∘ inits
    ≡⟨ cong (_∘ map tails ∘ inits) (cong (maximum ∘_) (map-promotion (sum))) ⟩
      maximum ∘ concat ∘ map (map sum) ∘ map tails ∘ inits
    ≡⟨ cong (_∘ inits) (cong ((maximum ∘ concat) ∘_) (map-compose (tails) (map sum))) ⟩
      maximum ∘ concat ∘ map (map sum ∘ tails) ∘ inits
    ≡⟨ cong (_∘ map(map sum ∘ tails) ∘ inits) (reduce-promotion _⊔_ 0 ℕ-⊔-is-monoid)  ⟩ -- ℕ-⊔-is-monoid
      maximum ∘ map maximum ∘ map (map sum ∘ tails) ∘ inits
    ≡⟨ cong (λ x → maximum ∘ x ∘ inits) (map-compose (map sum ∘ tails) maximum) ⟩
      maximum ∘ map (maximum ∘ map sum ∘ tails) ∘ inits
    ≡⟨ cong (λ x → maximum ∘ map x ∘ inits) (horner-rule _⊔_ 0 _+_ 0 monoid.ℕ-⊔-is-monoid monoid.ℕ-add-is-monoid +-distribʳ-⊔) ⟩
      maximum ∘ map (foldl maxadd 0) ∘ inits
    ≡⟨ cong(maximum ∘_) (sym(acc-lemma maxadd 0)) ⟩
      maximum ∘ (scanl maxadd 0)
    ≡⟨ refl ⟩
      mss-fast
    ∎
    
  -- derivation-alt : ∀ xs → mss xs ≡ (maximum ∘ (map sum ∘ concat) ∘ map tails ∘ inits) xs
  -- derivation-alt xs = refl

--  derivation-alt : mss ≡ (maximum ∘ concat ∘ map (map sum) ∘ map tails ∘ inits)
--  derivation-alt rewrite (map-promotion (map sum)) = refl
  -- rewrite ∘-assoc  (map tails ∘ inits) (concat) (map sum) | map-promotion (map sum)
  

  -- derivation = extensionality derivation-alt
  
  -- note: it is possible to avoid extensionality and instead prove the following
  --
  -- derivation-alt : ∀ xs → mss xs ≡ mss-fast xs
  -- derivation-alt = ?
  --
  -- In fact, this version should be slightly easier to write, since it (generally)
  -- produces better error messages. If you want to follow this route, go ahead and
  -- prove the above 'derivation-alt', and uncomment the following:
  --
  -- derivation : mss ≡ mss-fast
  -- derivation = extensionality derivation-alt

  -- bonus(hard): try to prove the same result for integers (instead of naturals)
  --
  -- Our effort is futile if every element in the list is non-negative, because
  -- the MSS will always be the sum of all elements. However, it is not trivial
  -- to prove the same result for integers, because 'maximum []' is usually defined
  -- as negative infinity (-∞), which is not an integer.
  --
  -- However, we can extend integers (ℤ) to ℤ∞ as follows:
  --
  --   data ℤ∞ : Set where
  --     fin : ℤ → ℤ∞
  --     -∞ : ℤ∞
  --
  -- and replace 0 with -∞ in 'maximum'. Now you should be able to prove the result.
  -- You will need to define operations like '_+_' and '_⊔_', and prove lemmas like
  -- '+-distribʳ-⊔' all by yourself, which, if you ask me, is not the most pleasant
  -- way to spend your afternoon.

  -- bonus(hard): try to prove the correctness of 'mss' and 'mss-fast'
  --
  -- We have this "segment" relation (you may come up with better definitions):
  --
  --   open import Data.List using (take; drop)
  --   infix 4 _⊆_
  --   data _⊆_ {A : Set} (xs : List A) (ys : List A) : Set where
  --     segment : ∀ m n → take m (drop n ys) ≡ xs → xs ⊆ ys
  --
  -- We also have the "less than" relation:
  --
  --   open import Data.Nat using (_≤_)
  --
  -- which is defined as follows in the standard library:
  --
  --   infix 4 _≤_
  --   data _≤_ : ℕ → ℕ → Set where
  --     z≤n : ∀ {n}                 → zero  ≤ n
  --     s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
  --
  -- 'mss' is proven to be correct if we can prove the following two theorems:
  --
  --   open import Data.Product using (_×_; ∃-syntax)
  --   mss-is-max : ∀ {xs ys} → ys ⊆ xs → sum ys ≤ mss xs
  --   mss-exists : ∀ {xs} → ∃[ ys ] ys ⊆ xs × sum ys ≡ mss xs

module BMF2-1 where

  open import Data.Product using (_×_; _,_; Σ-syntax; proj₁)
  open import Data.Nat using (ℕ; _+_; zero; suc)
  open import Data.List using (List; []; _∷_; [_]; _++_)
  open import Relation.Nullary using (¬_)

  infixr 5 _∷′_
  data NList (A : Set) : Set where
    [_]′ : (x : A) → NList A
    _∷′_ : (x : A) → (xs : NList A) → NList A

  infixr 5 _++′_
  _++′_ : ∀ {A : Set} → NList A → NList A → NList A
  [ x ]′ ++′ ys = x ∷′ ys
  (x ∷′ xs) ++′ ys = x ∷′ xs ++′ ys

  ++′-assoc : ∀ {A : Set} (xs ys zs : NList A) → (xs ++′ ys) ++′ zs ≡ xs ++′ ys ++′ zs
  ++′-assoc [ x ]′    ys zs = refl
  ++′-assoc (x ∷′ xs) ys zs = cong (x ∷′_) (++′-assoc xs ys zs)

  NList-++′-is-semigroup : ∀ {A : Set} → IsSemigroup {NList A} _++′_
  NList-++′-is-semigroup .assoc = ++′-assoc

  -- this reduce works on non-empty lists
  reduce : ∀ {A : Set} → (_⊕_ : A → A → A) → NList A → A
  reduce {A} _⊕_ [ x ]′ = x
  reduce {A} _⊕_ (x ∷′ xs) = x ⊕ reduce _⊕_ xs

  -- this map works on non-empty lists
  -- and it produces non-empty lists
  map : ∀ {A B : Set} → (f : A → B) → NList A → NList B
  map f [ x ]′ = [ f x ]′
  map f (x ∷′ xs) = f x ∷′ map f xs

  record IsHomomorphism
    {A : Set} {_⊕_ : A → A → A} (m₁ : IsSemigroup _⊕_)
    {B : Set} {_⊗_ : B → B → B} (m₂ : IsSemigroup _⊗_)
    (f : A → B) : Set where
    field
      distrib : (x y : A) → f (x ⊕ y) ≡ f x ⊗ f y

  open IsHomomorphism

  -- 1. prove 'split' is a homomorphism
  split : ∀ {A : Set} → NList A → List A × A
  split = reduce (λ _ z → z) ∘ map (_,_ [])

  -- bonus: you may also want to prove the following theorems:
  --
  --   _⊗_ : ∀ {A : Set} → List A × A → List A × A → List A × A
  --   R-is-semigroup : ∀ {A : Set} → IsSemigroup {List A × A} _⊗_
  --   split-is-homomorphism : ∀ {A : Set} → IsHomomorphism NList-++′-is-semigroup R-is-semigroup (split {A})
  --
  -- Alternatively, you may find it much more desirable (satisfactory) to prove the general case:
  --
  --   reduce-map-is-homomorphism : ∀ {A B : Set}
  --     → (f : A → B)
  --     → (_⊗_ : B → B → B)
  --     → (B-⊗-is-semigroup : IsSemigroup _⊗_)
  --       ---------------------------------------------------------------------------
  --     → IsHomomorphism NList-++′-is-semigroup B-⊗-is-semigroup (reduce _⊗_ ∘ map f)

  -- to verify your 'split' is correct. after defining 'split', proving the following
  -- should be as easy as filling in 'refl'.
  split-is-correct : split (1 ∷′ 2 ∷′ 3 ∷′ [ 4 ]′) ≡ (1 ∷ 2 ∷ 3 ∷ [] , 4)
  split-is-correct = {!!}

  -- bonus: find a proper way to prove your split is indeed correct:
  --
  --   split-is-indeed-correct : ∀ {A} xs
  --     → let (ys , z) = split {A} xs
  --       in xs ≡ ys ++ [ z ]

  -- 2. prove 'init' is not a homomorphism
  init : ∀ {A : Set} → NList A → List A
  init = proj₁ ∘ split

  -- This part might be too hard for you to prove in Agda, so you can choose
  -- to write this part in natural language. If so, comment out (or remove)
  -- the following code, and write your proof in the comments.
  --
  -- Anyway, below are some key points if you want to try to prove in Agda:
  -- (1) inequality 'x ≢ y' is negation of equality: '¬ (x ≡ y)'
  -- (2) negation '¬ x' is implication to falsity: 'x → ⊥'
  -- (3) falsity '⊥' is an empty data type, it has no constructors ...
  -- (4) ... which means we can pattern match with absurd pattern '()'

  init-is-not-homomorphism : ∀ {_⊗_} (m : IsSemigroup _⊗_)
    → ¬ IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  init-is-not-homomorphism {_⊗_} m H = {!!}

  -- Hint: you might want to follow this guideline below if you get stuck.
  --
  -- Step 1: interpret the theorem
  --   ¬ IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  -- is just another way of saying
  --   IsHomomorphism NList-++′-is-semigroup m (init {ℕ}) → ⊥
  -- (proof by contradiction)
  --
  -- Step 2: get your premise
  -- You want to derive contradiction from the premise, so the first thing
  -- to do is get the premise (add it as an argument):
  --   init-is-not-homomorphism {_⊗_} m H = ?
  -- Now we have the following premises:
  --   m : IsSemigroup _⊗_
  --   H : IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  --
  -- Step 3: derive absurd results
  -- Pass in some example to your premises, and try to get some absurd
  -- results such as 'K : [ 0 ] ≡ [ 42 ]'.
  --
  -- Step 4: show the absurdity by proving the negation
  -- e.g. for 'K : [ 0 ] ≡ [ 42 ]', write the following:
  --   ¬K : [ 0 ] ≢ [ 42 ]
  --   ¬K ()
  --
  -- Step 5: make use of that absurd result
  -- Use the result 'K' from Step 3, apply it to '¬K':
  --   ¬K K
  -- Just use this expression as the return value.
  -- Alternatively, there is a library function at our disposal:
  --   open import Relation.Nullary using (contradiction)
  --   contradiction K ¬K
