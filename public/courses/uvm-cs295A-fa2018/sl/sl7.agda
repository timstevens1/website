{-
Name: ⁇
Date: ⁇

Collaboration Statement:
«Write your collaboration statement here…»
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to blackboard as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- statement above, as indicated by the course course collaboration
-- policy:
--
--     Collaboration on the high-level ideas and approach on
--     assignments is encouraged. Copying someone else's work is not
--     allowed. Any collaboration, even at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration statement. E.g., "I discussed
--     high-level strategies for solving problem 2 and 5 with Alex."
--     Students caught copying work are eligible for immediate failure
--     of the course and disciplinary action by the University. All
--     academic integrity misconduct will be treated according to
--     UVM's Code of Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

module sl7 where

open import Basics-v2

-- sorted specification --

module _ {A : Set} {{_ : has[<] A}} where

  data _≤[List]_ (x : A) : List A → Set where
    [] : x ≤[List] []
    ⟨_⟩ : ∀ {y ys}
      → x ≤ y
      → x ≤[List] (y ∷ ys)
  
  data Sorted : List A → Set where
    [] : Sorted []
    _∷_ : ∀ {x xs}
      → x ≤[List] xs
      → Sorted xs
      → Sorted (x ∷ xs)

-- accessibility and well founded --

data Acc {A : Set} (_≺_ : A → A → Set) (x : A) : Set where
  acc : (∀ {y} → y ≺ x → Acc _≺_ y) → Acc _≺_ x

WF : ∀ {A : Set} → (A → A → Set) → Set
WF _≺_ = ∀ x → Acc _≺_ x

<ᴺ-wf′ : ∀ {m} (n : ℕ) → m < n → Acc _<_ m
<ᴺ-wf′ zero ()
<ᴺ-wf′ (suc n) zero = acc λ where ()
<ᴺ-wf′ (suc n) (suc ε) = acc λ where ε′ → (<ᴺ-wf′ n) (<-trans-l _ _ n (≤-fr-< ε′) ε)

<ᴺ-wf : ∀ (n : ℕ) → Acc _<_ n
<ᴺ-wf n = acc (<ᴺ-wf′ n)

-- merge sort --

module _ {A : Set} {{_ : has[<?] A}} where

  split : A → A → List A → List A ∧ List A
  split w x [] = ⟨ [ w ] , [ x ] ⟩
  split w x [ y ] = ⟨ [ w , x ] , [ y ] ⟩
  split w x (y ∷ z ∷ xs) = let ⟨ ys , zs ⟩ = split y z xs in ⟨ w ∷ ys , x ∷ zs ⟩

  split-length : ∀ (x y : A) (xs : List A) → let ⟨ ys , zs ⟩ = split x y xs in length ys < length (x ∷ y ∷ xs) ∧ length zs < length (x ∷ y ∷ xs)
  split-length w x [] = ⟨ suc zero , suc zero ⟩
  split-length w x [ y ] = ⟨ suc (suc zero) , suc zero ⟩
  split-length w x (y ∷ z ∷ xs) with split y z xs | split-length y z xs
  … | ⟨ ys , zs ⟩ | ⟨ IH₁ , IH₂ ⟩ = ⟨ suc (<ᴺ-lmono _ 1 _ IH₁) , suc (<ᴺ-lmono _ 1 _ IH₂) ⟩

  merge : List A → List A → List A
  merge [] ys = ys
  merge xs [] = xs
  merge (x ∷ xs) (y ∷ ys) with x ≤? y
  … | LE = x ∷ merge xs (y ∷ ys)
  … | GT = y ∷ merge (x ∷ xs) ys

  msort′ : ∀ (xs : List A) → Acc _<_ (length xs) → List A
  msort′ [] ε = []
  msort′ [ x ] ε = [ x ]
  msort′ (x ∷ y ∷ xs) (acc r) =
    let ⟨ ys , zs ⟩ = split x y xs
        ⟨ H₁ , H₂ ⟩ = split-length x y xs
    in merge (msort′ ys (r H₁)) (msort′ zs (r H₂))

  msort : List A → List A
  msort xs = msort′ xs (<ᴺ-wf (length xs))

-- verification of merge sort --

module _ {A : Set} {{_ : has[<?] A}} {{_ : has[<] A}} {{_ : cor[<?] A}} {{_ : cor[<] A}} where

  merge-bounded : ∀ (x : A) (xs ys : List A) → x ≤[List] xs → x ≤[List] ys → x ≤[List] (merge xs ys)
  merge-bounded x [] ys ε₁ ε₂ = ε₂
  merge-bounded x (y ∷ ys) [] ε₁ ε₂ = ε₁
  merge-bounded x (y ∷ ys) (z ∷ zs) ⟨ ε₁ ⟩ ⟨ ε₂ ⟩ with y ≤? z
  … | LE = ⟨ ε₁ ⟩
  … | GT = ⟨ ε₂ ⟩

  merge-sorted : ∀ (xs ys : List A) → Sorted xs → Sorted ys → Sorted (merge xs ys)
  merge-sorted [] _ [] ε₂ = ε₂
  merge-sorted _ [] (ε₁ ∷ εs₁) [] = ε₁ ∷ εs₁
  merge-sorted (x ∷ xs) (y ∷ ys) (ε₁ ∷ εs₁) (ε₂ ∷ εs₂) with x ≤? y | x ≤* y | x ≤~ y
  … | LE | LE ε | LE = merge-bounded x xs (y ∷ ys) ε₁ ⟨ ε ⟩ ∷ merge-sorted xs (y ∷ ys) εs₁ (ε₂ ∷ εs₂)
  … | GT | GT ε | GT = merge-bounded y (x ∷ xs) ys ⟨ <-weaken y x ε ⟩ ε₂ ∷ merge-sorted (x ∷ xs) ys (ε₁ ∷ εs₁) εs₂

  msort′-sorted : ∀ (xs : List A) (ε : Acc _<_ (length xs)) → Sorted (msort′ xs ε)
  msort′-sorted [] ε = []
  msort′-sorted [ x ] ε = [] ∷ []
  msort′-sorted (x ∷ y ∷ xs) (acc r) with split x y xs | split-length x y xs
  … | ⟨ ys , zs ⟩ | ⟨ H₁ , H₂ ⟩ = merge-sorted (msort′ ys (r H₁)) (msort′ zs (r H₂)) (msort′-sorted ys (r H₁)) (msort′-sorted zs (r H₂))

  msort-sorted : ∀ (xs : List A) → Sorted (msort xs)
  msort-sorted xs = msort′-sorted xs (<ᴺ-wf (length xs))
