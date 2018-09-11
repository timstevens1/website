module ic5 where

-------------
-- LIBRARY --
-------------

infix 4 _≡_
infixl 6 _+_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-runit : ∀ (m : ℕ) → m + zero ≡ m
  +-rsuc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

--------------
-- IN CLASS --
--------------

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  -- --------------
  -- zero ≤ n
  --
  -- m ≤ n
  -- -----------------
  -- suc m ≤ suc n

_ : 2 ≤ 5
_ = {!!}

_ : 2 ≤ 5
_ = {!!}

_ : 2 ≤ 5
_ = {!!}

_ : 5 ≤ 5
_ = {!!}
    
≤-refl : ∀ (n : ℕ) → n ≤ n
≤-refl n = {!!}

≤-trans : ∀ (m n p : ℕ) → n ≤ p → m ≤ n → m ≤ p
≤-trans m n p n≤p m≤n = {!!}

≤-antisym : ∀ (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
≤-antisym m n m≤n n≤m = {!!}

data Total (m n : ℕ) : Set where
  -- m ≤ n
  -- -----------
  -- Total m n
  --
  -- n ≤ m
  -- -----------
  -- Total m n

data Total′ : ℕ → ℕ → Set where
  -- m ≤ n
  -- -----------
  -- Total m n
  --
  -- n ≤ m
  -- -----------
  -- Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total m n = {!!}

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ m n = {!!}

≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m n = {!!}

+-≤-rmono : ∀ (m n p : ℕ) → n ≤ p → m + n ≤ m + p
+-≤-rmono m n p n≤p = {!!}

+-≤-lmono : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-≤-lmono m n p n≤p = {!!}

+-≤-lmono′ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-≤-lmono′ m n p m≤n = {!!}

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  -- ------------
  -- zero < suc n
  --
  -- m < n
  -- -------------
  -- suc m < suc n

_ : 2 < 5
_ = {!!}

_ : 4 < 5
_ = {!!}

mutual 
  data even : ℕ → Set where
    -- -------------
    -- even zero
    --
    -- odd n
    -- -------------
    -- even (suc n)
  data odd : ℕ → Set where
    -- even n
    -- -------------
    -- odd (suc n)

even[4] : even 4
even[4] = {!!}

odd[5] : odd 5
odd[5] = {!!}

mutual
  e+e≡e : ∀ (m n : ℕ) → even m → even n → even (m + n)
  e+e≡e m n e[m] e[n] = {!!}

  o+e≡e : ∀ (m n : ℕ) → odd m → even n → odd (m + n)
  o+e≡e m n e[m] e[n] = {!!}


e+e≡e′ : ∀ (m n : ℕ) → even m → even n → even (m + n)
e+e≡e′ m n e[m] e[n] = {!!}
