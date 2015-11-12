
module NoFib.IO where

open import Prelude

private
  usage : IO ⊤
  usage = getProgName >>= λ prog →
          putStrLn $ "Usage: " & prog & " N"

withNatArg : (Nat → IO ⊤) → IO ⊤
withNatArg f = getArgs >>= λ
  { (s ∷ []) →
    case parseNat s of λ
    { (just n) → f n
    ; nothing  → usage
    }
  ; _ → usage
  }

