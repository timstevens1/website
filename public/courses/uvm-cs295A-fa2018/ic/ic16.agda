module ic16 where

open import Basics-v4

data color : Set where
  R : color
  B : color

data rbt : Set where
  Leaf : rbt
  [_/_/_] : color → rbt → rbt → rbt

data black-nodes : rbt → ℕ → Set where

data red-children : rbt → Set where

t1 : rbt
t1 = [ {!!} / [ {!!} / [ {!!} / Leaf / Leaf ]
                     / Leaf ]
            / [ {!!} / Leaf / Leaf ] ]

_ : black-nodes t1 {!!}
_ = {!!}

_ : red-children t1
_ = {!!}

_ : black-nodes t1 2 ∧ red-children t1
_ = {!!}

t2 : rbt
t2 = [ {!!} / [ {!!} / [ {!!} / Leaf / Leaf ]
                     / Leaf ]
            / Leaf ]

_ : black-nodes t2 {!!}
_ = {!!}

_ : red-children t2
_ = {!!}

balance : color → rbt → rbt → rbt
balance c t₁ t₂ = {!!}

push : rbt → rbt
push = {!!}
