
module ReverseComplement where

open import Prelude

postulate
  unsafeInterleaveIO : {A : Set} → IO A → IO A

{-# IMPORT System.IO.Unsafe #-}
{-# COMPILED unsafeInterleaveIO \ _ -> System.IO.Unsafe.unsafeInterleaveIO #-}

{-# IMPORT Data.Text.IO #-}
postulate
  Handle  : Set
  getLine : IO String
  stdin   : Handle
  isEOF   : Handle → IO Bool

{-# IMPORT System.IO #-}
{-# COMPILED_TYPE Handle  System.IO.Handle #-}
{-# COMPILED      getLine Data.Text.IO.getLine #-}
{-# COMPILED      isEOF   System.IO.hIsEOF #-}
{-# COMPILED      stdin   System.IO.stdin #-}

{-# NON_TERMINATING #-}
getLines : IO (List String)
getLines =
  isEOF stdin >>=
  (if_then pure [] else
    forM s ← getLine do
    s ∷_ <$> unsafeInterleaveIO getLines
  )

echo : List String → IO ⊤
echo []       = return _
echo (x ∷ xs) = putStrLn x >> echo xs

main = echo =<< getLines
