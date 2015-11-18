
module Data.FloatArray where

open import Prelude
open import Builtin.Float

{-# IMPORT Foreign #-}
{-# IMPORT Foreign.Storable #-}
{-# IMPORT Foreign.Marshal.Alloc #-}
{-# IMPORT Data.IORef #-}

private
 postulate
  Ptr         : Set → Set
  peek        : Ptr Float → Nat → IO Float
  poke        : Ptr Float → Nat → Float → IO ⊤
  mallocArray : Nat → IO (Ptr Float)

{-# COMPILED_TYPE Ptr Foreign.Ptr #-}
{-# COMPILED peek        \ p n   -> Foreign.Storable.peekElemOff p (fromInteger n) #-}
{-# COMPILED poke        \ p n x -> Foreign.Storable.pokeElemOff p (fromInteger n) x #-}
{-# COMPILED mallocArray \ n     -> Foreign.Marshal.Alloc.mallocBytes
                                      (fromInteger n * Foreign.Storable.sizeOf (0.0 :: Double)) #-}

data Array (n : Nat) : Set where
  ptr : Ptr Float → Array n

private
  unptr : ∀ {n} → Array n → Ptr Float
  unptr (ptr p) = p

read : ∀ {n} {A : Set} → Ptr Float → Nat → (Vec Float n → IO A) → IO A
read {zero } p _ k = k []
read {suc n} p i k = peek p i >>= λ x → read p (suc i) (k ∘ (x ∷_))

write : ∀ {n} → Ptr Float → Nat → Vec Float n → IO ⊤
write p i [] = return _
write p i (x ∷ xs) = poke p i x >> write p (suc i) xs

onArray : ∀ {n} → (Vec Float n → Vec Float n) → Array n → IO ⊤
onArray f p = read (unptr p) 0 λ xs → write (unptr p) 0 (f xs)

allocArray : ∀ {n} → Vec Float n → IO (Array n)
allocArray {n} xs =
  forM p ← mallocArray n do
  ptr p <$ write p 0 xs

readArray : ∀ {n} → Array n → IO (Vec Float n)
readArray (ptr p) = read p 0 return
