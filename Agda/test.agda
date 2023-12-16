module test where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
----- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_;_≤_; s)
----- open import Data.Nat.Properties using (+-comm; +-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; +-comm; *-comm )

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n _ =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  rewrite ≤-antisym m≤n n≤m = refl

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
  
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q

+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-distri : (n p : ℕ)
  → (suc n) * p ≡ p + n * p

*-distri zero p = refl
*-distri (suc n) p rewrite *-distri n p = refl

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    ------------
  → n * p ≤ n * q

*-monoʳ-≤ zero p q _ = z≤n
*-monoʳ-≤ (suc n) p q p≤q rewrite *-distri n p | *-distri n q = +-mono-≤ p q (n * p) (n * q) p≤q(*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    ------------
  → p * n ≤ q * n

*-monoˡ-≤ n p q p≤q rewrite *-comm p n | *-comm q n = *-monoʳ-≤ n p q p≤q

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-trans : ∀ {m n q : ℕ}
  → m < n
  → n < q
  → m < q

<-trans z<s (s<s n<q) = z<s
<-trans (s<s m<n) (s<s n<q) = s<s(<-trans m<n n<q)

