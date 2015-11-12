
module Data.Stream where

open import Prelude

record Stream {a} (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field head : A
        tail : Stream A

open Stream public

takeS : ∀ {a} {A : Set a} → Nat → Stream A → List A
takeS zero    xs = []
takeS (suc n) xs = head xs ∷ takeS n (tail xs)

dropS : ∀ {a} {A : Set a} → Nat → Stream A → Stream A
dropS zero    xs = xs
dropS (suc n) xs = dropS n (tail xs)

iterate : ∀ {a} {A : Set a} → (A → A) → A → Stream A
head (iterate f x) = x
tail (iterate f x) = iterate f (f x)

mapS : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)

instance
  FunctorS : ∀ {a} → Functor (Stream {a})
  fmap {{FunctorS}} = mapS

  ApplicativeS : ∀ {a} → Applicative (Stream {a})
  pure  {{ApplicativeS}} = iterate id
  head (_<*>_ {{ApplicativeS}} fs xs) = head fs (head xs)
  tail (_<*>_ {{ApplicativeS}} fs xs) = tail fs <*> tail xs

