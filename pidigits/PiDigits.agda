
module PiDigits where

open import Prelude
open import Control.WellFounded
open import Data.Stream
open import NoFib.IO

-- Let's not worry about division by zero.
_div!_ : Int → Int → Int
a div! b = quotInt-by b {{nonZ}} a
  where postulate nonZ : NonZeroInt b
{-# INLINE _div!_ #-}

output : Int → Int → Int → Maybe Int
output q r t with r - q
... | negsuc _ = nothing
... | pos    _ with q * 3 + r
...   | a with a div! t
...     | n with (n + 1) * t - (q + a)
...       | negsuc _ = nothing
...       | pos    _ = just n
{-# INLINE output #-}

{-# TERMINATING #-}
-- We trust Jeremy when he says this is productive.
pi : Int → Int → Int → Int → Stream Int
pi q r t k with output q r t
... | nothing = case 2 * k + 1 of λ j →
                pi (q * k) ((2 * q + r) * j)
                   (t * j) (k + 1)
... | just n = n ∷ pi (10 * q) (10 * (r - t * n)) t k

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

main = withNatArg λ n → mapM! putStrLn $ lines n 0 $ takeS n (pi 1 0 1 1)
