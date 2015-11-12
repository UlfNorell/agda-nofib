
module PiDigits where

open import Prelude
open import Control.WellFounded
open import Data.Stream

module _ {A B C : Set} (next : B → C) (safe : B → C → Bool)
                       (prod : B → C → B) (cons : B → A → B) where

  {-# TERMINATING #-}
  stream : (z : B) (xs : Stream A) → Stream C
  stream z xs with next z
  ... | y with safe z y
  ...   | false = stream (cons z (head xs)) (tail xs)
  ...   | true  = y ∷ stream (prod z y) xs

from : Int → Stream Int
from = iterate (1 +_)

data LFT : Set where
  ⟨_,_,_,_⟩ : (a b c d : Int) → LFT

extr : LFT → Int → Int
extr ⟨ q , r , s , t ⟩ x = quotInt-by (s * x + t) {{nonZ}} (q * x + r)
  where postulate nonZ : NonZeroInt _

I : LFT
I = ⟨ 1 , 0 , 0 , 1 ⟩

_∙_ : LFT → LFT → LFT
⟨ q , r , s , t ⟩ ∙ ⟨ u , v , w , x ⟩ =
  ⟨ q * u + r * w , q * v + r * x
  , s * u + t * w , s * v + t * x ⟩

pi : Stream Int
pi = stream next safe prod _∙_ I lfts
  where
    lfts : Stream LFT
    lfts = fmap (λ k → ⟨ k , 4 * k + 2 , 0 , 2 * k + 1 ⟩) (from 1)
    next = λ z   → extr z 3
    safe = λ z n → isYes (n == extr z 4)
    prod = λ z n → ⟨ 10 , -10 * n , 0 , 1 ⟩ ∙ z

append : List String → String
append = foldr _&_ ""

lines : Nat → Nat → List Int → List String
lines zero    _     _  = []
lines _       _     [] = []
lines (suc n) count xs with splitAt 10 xs
... | (ys , zs) with length ys
...   | k = (append (map show ys) & packString (replicate (10 - k) ' ') & "\t:" & show (count + k)) ∷
            lines n (count + 10) zs

mapM! : {M : Set → Set} {A : Set} {{_ : Monad M}} → (A → M ⊤) → List A → M ⊤
mapM! f []       = return _
mapM! f (x ∷ xs) = f x >> mapM! f xs

withNatArg : (Nat → IO ⊤) → IO ⊤
withNatArg f = getArgs >>= λ
  { (s ∷ []) →
    case parseNat s of λ
    { (just n) → f n
    ; nothing  → putStrLn "Usage: PiDigits N"
    }
  ; _ → putStrLn "Usage: PiDigits N"
  }

main = withNatArg λ n → mapM! putStrLn $ lines n 0 $ takeS n pi
