module HW15 where

-- How to input the Unicode characters
-- ===================================
-- ℕ    \bN
-- →    \->
-- ∷    \::
-- ≡    \==
-- ⟨    \<
-- ⟩    \>
-- ˘    \u{}

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

-- Chap. 18

-- problem 1.1: commutativity of _*_
*+zero : (x : ℕ) → x + zero ≡ x
*+zero zero = refl
*+zero (suc x) rewrite *+zero x = refl

*+suc : (x y : ℕ) → x + (suc y) ≡ suc (x + y)
*+suc zero y = refl
*+suc (suc x) y rewrite *+suc x y = refl

*+swap : (x y : ℕ) → x + y ≡ y + x
*+swap x zero rewrite *+zero x = refl
*+swap x (suc y) rewrite *+suc x y | *+swap x y = refl

*+assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
*+assoc zero y z = refl
*+assoc (suc x) y z rewrite *+assoc x y z = refl

**zero : (x : ℕ) → x * zero ≡ zero
**zero zero = refl
**zero (suc x) rewrite (**zero x) = refl

*+*assoc : (x y : ℕ) -> x * (suc y) ≡ x + x * y
*+*assoc zero y  rewrite **zero y = refl
*+*assoc (suc x) y  rewrite *+*assoc x y | *+assoc y x (x * y) | *+assoc x y (x * y) | *+swap x y = refl

*-comm : (x y : ℕ) → x * y ≡ y * x
*-comm zero y rewrite **zero y = refl
*-comm (suc x) y rewrite *-comm x y | *+*assoc y x = refl

-- problem 1.2: associativity of _*_
*+rerange : (x y z k : ℕ) -> (x + y) + (z + k) ≡ x + (y + z) + k
*+rerange x y z k rewrite *+assoc (x + y) z k | *+assoc x y z = refl

**distri : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
**distri x y zero rewrite **zero (x + y) | **zero x | **zero y = refl
**distri x y (suc z) rewrite *+*assoc x z | *+*assoc y z | *+*assoc (x + y) z | **distri x y z | *+rerange x y (x * z) (y * z) | *+swap y (x * z) | *+rerange x (x * z) y (y * z) = refl

*-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
*-assoc zero y z rewrite **zero y | **zero (y * z) = refl
*-assoc (suc x) y z rewrite *-assoc x y z | **distri y (x * y) z | *-assoc x y z = refl

-- problem 2: prove the theorems.
-- remark: the standard library provides the following comparison based on decidability
--   _<?_ : (x y : ℕ) → Dec (x < y)
-- where `Dec` is the type for decidability;
-- and also the following comparison as inductive relation
--   _<_ : (x y : ℕ) → Set
-- so neither is the one we want.
-- note: read more on decidability here:
--  * stdlib: https://agda.github.io/agda-stdlib/Relation.Nullary.Decidable.Core.html#1476
--  * PLFA: https://plfa.github.io/Decidable/
-- so we just provide the same definition as given in the slides:
-- (note that stdlib use (Bool; true; false) instead of (𝔹; tt; ff))
infix 9 _≟_
_≟_ : (x y : ℕ) → Bool
zero  ≟ zero  = true
zero  ≟ suc _ = false
suc _ ≟ zero  = false
suc x ≟ suc y = x ≟ y

infix 9 _<_
_<_ : (x y : ℕ) → Bool
zero < zero  = false
zero < suc _ = true
suc _ < zero  = false
suc x < suc y = x < y

-- problem 2.1
n≮n : (n : ℕ) → n < n ≡ false
n≮n zero = refl
n≮n (suc x) rewrite n≮n x = refl

-- problem 2.2
<-antisym : (x y : ℕ) → x < y ≡ true → y < x ≡ false
<-antisym 0 0 p = refl
<-antisym (suc x) 0 ()
<-antisym 0 (suc x) p = refl
<-antisym (suc x) (suc y) p = <-antisym x y p

-- problem 2.3
<-trichotomy : (x y : ℕ) → x < y ∨ x ≟ y ∨ y < x ≡ true
<-trichotomy 0 0 = refl
<-trichotomy 0 (suc y) = refl
<-trichotomy (suc x) 0 = refl
<-trichotomy (suc x) (suc y) rewrite <-trichotomy x y = refl

-- Chap. 19

-- I am feeling lazy today, so let's just introduce the variables here.
-- This is equivalent to adding a `(A : Set)` to every type with a free variable `A`
variable
  A : Set

takeWhile : (p : A → Bool) → List A → List A
takeWhile _ []  = []
takeWhile p (x ∷ l) with p x
takeWhile p (x ∷ l) | true = x ∷ takeWhile p l
takeWhile p (x ∷ l) | false = []

-- this function is usually named `replicate` instead of `repeat`
replicate : ℕ → A → List A
replicate 0 _ = []
replicate (suc n) a = a ∷ replicate n a

prop : (a : A) (n : ℕ)
  → (p : A → Bool)
  → p a ≡ true
    -------------------------------------
  → takeWhile p (replicate n a) ≡ replicate n a
prop a 0 p = λ _ → refl
prop a (suc n) p fl rewrite fl | prop a n p fl = refl

