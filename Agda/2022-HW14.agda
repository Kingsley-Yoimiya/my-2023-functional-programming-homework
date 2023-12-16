module 2022-HW14 where

-- How to input the Unicode characters
-- ===================================
-- ℕ    \bN
-- →    \->
-- ∷    \::
-- ≡    \==
-- ⟨    \<
-- ⟩    \>
-- ˘    \u{}

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

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
