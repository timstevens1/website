module ic9 where

---------
-- LIB --
---------

infix 4 _≡_
infixl 6 _+_ _∸_
infixl 7 _*_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n     =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m
zero    ∸ (suc n)  =  zero
(suc m) ∸ (suc n)  =  m ∸ n

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ} → zero ≤ n
  suc : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ} → zero < suc n
  suc : ∀ {m n : ℕ} → m < n → suc m < suc n

infixr 2 _×_
data _×_ : Set → Set → Set where
  ⟨_,_⟩ : ∀ {A B : Set}
    → A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

infix 1 _⊎_
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

infix 20 ¬_
¬_ : Set → Set
¬ A = A → ⊥

postulate
  -- + --
  +-runit : ∀ (m : ℕ) → m + zero ≡ m
  +-rsuc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-assoc : ∀ (m n p : ℕ) → m + n + p ≡ m + (n + p)
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  -- * --
  *-rzero : ∀ (m : ℕ) → m * zero ≡ zero
  *-runit : ∀ (m : ℕ) → m * 1 ≡ m
  *-rsuc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
  *-assoc : ∀ (m n p : ℕ) → m * n * p ≡ m * (n * p)
  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
  -- ≤ --
  ≤-refl : ∀ (m : ℕ) → m ≤ m
  ≤-trans : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
  ≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
  -- < --
  <-irrefl : ∀ (m : ℕ) → ¬ (m ≤ m)
  <-trans : ∀ {m n p : ℕ} → n < p → m < n → m < p
  <-asym : ∀ {m n : ℕ} → ¬ (m < n × n < m)

--------------
-- IN CLASS --
--------------

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤?_
_≤?_ : ℕ → ℕ → Bool
m ≤? n = {!!}

_ : 2 ≤ 4
_ = {!!}

_ : (2 ≤? 4) ≡ true
_ = {!!}

_ : 10 ≤ 10
_ = {!!}

_ : (10 ≤? 10) ≡ true
_ = {!!}

cor[≤?]-L : ∀ {m n : ℕ} → m ≤ n → (m ≤? n) ≡ true
cor[≤?]-L ε = {!!}

cor[≤?]-R : ∀ (m n : ℕ) → (m ≤? n) ≡ true → m ≤ n
cor[≤?]-R m n = {!!}

data Ordering (m n : ℕ) : Set where
  LT : m < n → Ordering m n
  EQ : m ≡ n → Ordering m n
  GT : n < m → Ordering m n

_⋚_ : ∀ (m n : ℕ) → Ordering m n
m ⋚ n = {!!}

_ : 2 ⋚ 4 ≡ LT (suc (suc zero))
_ = {!!}
  
data Comparison : Set where
  LT : Comparison
  EQ : Comparison
  GT : Comparison

_⋚?_ : ℕ → ℕ → Comparison
m ⋚? n = {!!}

_ : 2 ⋚? 4 ≡ LT
_ = {!!}

data Link {m n : ℕ} : Comparison → Ordering m n → Set where
  LT : ∀ {ε : m < n} → Link LT (LT ε)
  EQ : ∀ {ε : m ≡ n} → Link EQ (EQ ε)
  GT : ∀ {ε : n < m} → Link GT (GT ε)

cor[⋚?]-L : ∀ (m n : ℕ) → Link (m ⋚? n) (m ⋚ n)
cor[⋚?]-L m n = {!!}

infixr 5 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ [ b ]
pattern [_,_,_] a b c = a ∷ [ b , c ]
pattern [_,_,_,_] a b c d = a ∷ [ b , c , d ]
pattern [_,_,_,_,_] a b c d e = a ∷ [ b , c , d , e ]
pattern [_,_,_,_,_,_] a b c d e f = a ∷ [ b , c , d , e , f ]
pattern [_,_,_,_,_,_,_] a b c d e f g = a ∷ [ b , c , d , e , f , g ]
pattern [_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ [ b , c , d , e , f , g , h ]
pattern [_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ [ b , c , d , e , f , g , h , i ]
pattern [_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ [ b , c , d , e , f , g , h , i , j ]

_ : List ℕ
_ = [ 0 , 1 , 2 ]

infixl 6 _⧺_
_⧺_ : ∀ {A : Set} → List A → List A → List A
xs ⧺ ys = {!!}

_ : [ 1 , 2 ] ⧺ [ 3 , 4 ] ≡ [ 1 , 2 , 3 , 4 ]
_ = {!!}

⧺-lunit : ∀ {A : Set} (xs : List A) → [] ⧺ xs ≡ xs
⧺-lunit xs = {!!}

⧺-runit : ∀ {A : Set} (xs : List A) → xs ⧺ [] ≡ xs
⧺-runit xs = {!!}

⧺-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ⧺ ys) ⧺ zs ≡ xs ⧺ (ys ⧺ zs)
⧺-assoc xs ys zs = {!!}

length : ∀ {A : Set} → List A → ℕ
length xs = {!!}

⧺-length : ∀ {A : Set} (xs ys : List A) → length (xs ⧺ ys) ≡ length xs + length ys
⧺-length xs ys = {!!}

reverse : ∀ {A : Set} → List A → List A
reverse xs = {!!}

shunt : ∀ {A : Set} → List A → List A → List A
shunt xs ys = {!!}

shunt-reverse-strong : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ⧺ ys
shunt-reverse-strong xs ys = {!!}

shunt-reverse : ∀ {A : Set} (xs : List A) → shunt xs [] ≡ reverse xs
shunt-reverse xs = {!!}

map : ∀ {A B : Set} → (A → B) → List A → List B
map f xs = {!!}

sucs : List ℕ → List ℕ
sucs xs = {!!}

_ : sucs [ 1 , 2 , 3 ] ≡ [ 2 , 3 , 4 ]
_ = {!!}

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr f i xs = {!!}

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = {!!}

_ : foldr _*_ 1 [ 1 , 2 , 3 , 4 ] ≡ 24
_ = {!!}

_ : foldr (λ x xs → x ∷ xs) [] [ 1 , 2 , 3 ] ≡ [ 1 , 2 , 3 ]
_ = {!!}

foldl : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldl f i xs = {!!}


_ : foldl _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = {!!}

_ : foldl _*_ 1 [ 1 , 2 , 3 , 4 ] ≡ 24
_ = {!!}

_ : foldl (λ x xs → x ∷ xs) [] [ 1 , 2 , 3 ] ≡ [ 3 , 2 , 1 ]
_ = {!!}
