
module N-Body where

open import Prelude
open import Builtin.Float
open import Text.Printf
open import NoFib.IO
open import Data.FloatArray

data Pos : Set where
  ⟨_,_,_⟩ : (x y z : Float) → Pos

Vel = Pos

_∙_ : Pos → Pos → Float
⟨ x , y , z ⟩ ∙ ⟨ x₁ , y₁ , z₁ ⟩ = x * x₁ + y * y₁ + z * z₁
{-# INLINE _∙_ #-}

diag : Float → Pos
diag x = ⟨ x , x , x ⟩
{-# INLINE diag #-}

mapP : (Float → Float) → Pos → Pos
mapP f ⟨ x , y , z ⟩ = ⟨ f x , f y , f z ⟩
{-# INLINE mapP #-}

zipP : (Float → Float → Float) → Pos → Pos → Pos
zipP f ⟨ x , y , z ⟩ ⟨ x₁ , y₁ , z₁ ⟩ = ⟨ f x x₁ , f y y₁ , f z z₁ ⟩
{-# INLINE zipP #-}

instance
  SemiringPos : Semiring Pos
  zro {{SemiringPos}} = diag 0.0
  one {{SemiringPos}} = diag 1.0
  _+_ {{SemiringPos}} u v = zipP _+_ u v
  _*_ {{SemiringPos}} u v = zipP _*_ u v

  SubPos : Subtractive Pos
  negate {{SubPos}} = mapP negate
  _-_    {{SubPos}} u v = zipP _-_ u v

  FracPos : Fractional Pos
  Fractional.Constraint FracPos _ _ = ⊤
  _/_ {{FracPos}} u v = zipP (λ x y → x / y) u v

∣_∣² : Pos → Float
∣ ⟨ x , y , z ⟩ ∣² = x * x + y * y + z * z
{-# INLINE ∣_∣² #-}

∣_∣ : Pos → Float
∣ v ∣ = sqrt ∣ v ∣²
{-# INLINE ∣_∣ #-}

daysPerYear : Float
daysPerYear = 365.24

solarMass : Float
solarMass = 4 * π ^ 2

record Body : Set where
  no-eta-equality
  constructor ⟨_,_,_⟩
  field
    p : Pos
    v : Vel
    m : Float

sumV : ∀ {a n} {A : Set a} {{_ : Semiring A}} → Vec A n → A
sumV []       = zro
sumV (x ∷ xs) = x + sumV xs

energy : ∀ {n} → Vec Body n → Float
energy = go 0.0
  where
    go : ∀ {n} → Float → Vec Body n → Float
    go e []       = e
    go e (b ∷ bs) = go (e + 0.5 * m * (v ∙ v) -
                        sumV (for bs λ b₁ → (m * Body.m b₁) / ∣ p - Body.p b₁ ∣)) bs
      where open Body b

infix 0 letstrict
syntax letstrict x (λ y → z) = let! y := x !in z
letstrict : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
letstrict x f = force x f
{-# INLINE letstrict #-} -- makes it 15% slower!

infix 0 letlazy
syntax letlazy x (λ y → z) = let~ y := x ~in z
letlazy : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
letlazy x f = f x
{-# INLINE letlazy #-}

-- Planets --

jupiter : Body
jupiter = ⟨ ⟨ 4.84143144246472090 , -1.16032004402742839 , -1.03622044471123109e-01 ⟩
          , ⟨ 1.66007664274403694e-03 , 7.69901118419740425e-03 , -6.90460016972063023e-05 ⟩ * diag daysPerYear
          , 9.54791938424326609e-04 * solarMass ⟩

saturn : Body
saturn = ⟨ ⟨ 8.34336671824457987e+00 ,  4.12479856412430479e+00 , -4.03523417114321381e-01 ⟩
         , ⟨ -2.76742510726862411e-03 ,  4.99852801234917238e-03 ,  2.30417297573763929e-05 ⟩ * diag daysPerYear
         , 2.85885980666130812e-04 * solarMass ⟩

uranus : Body
uranus = ⟨ ⟨ 1.28943695621391310e+01 , -1.51111514016986312e+01 , -2.23307578892655734e-01 ⟩
         , ⟨ 2.96460137564761618e-03 ,  2.37847173959480950e-03 , -2.96589568540237556e-05 ⟩ * diag daysPerYear
         , 4.36624404335156298e-05 * solarMass ⟩

neptune : Body
neptune = ⟨ ⟨ 1.53796971148509165e+01 , -2.59193146099879641e+01 , 1.79258772950371181e-01 ⟩
          , ⟨ 2.68067772490389322e-03 ,  1.62824170038242295e-03 , -9.51592254519715870e-05 ⟩ * diag daysPerYear
          , 5.15138902046611451e-05 * solarMass ⟩

sun : Body
Body.p sun = diag 0
Body.v sun = diag 0
Body.m sun = solarMass

offsetMomentum : Pos → Body → Body
offsetMomentum p b = record { Body b; v = negate (p / diag solarMass) }

numBodies : Nat
numBodies = 5

bodies : Vec Body numBodies
bodies = offsetMomentum p sun ∷ planets
  where
    planets : Vec Body _
    planets = jupiter ∷ saturn ∷ uranus ∷ neptune ∷ []
    p : Pos
    p = sumV (fmap (λ b →  Body.v b * diag (Body.m b)) (sun ∷ planets))


posToList : Pos → Vec Float 3
posToList ⟨ x , y , z ⟩ = x ∷ y ∷ z ∷ []

listToPos : Vec Float 3 → Pos
listToPos (x ∷ y ∷ z ∷ []) = ⟨ x , y , z ⟩

bodyToList : Body → Vec Float 7
bodyToList ⟨ p , v , m ⟩ = posToList p v++ posToList v v++ m ∷ []

splitV : ∀ {a} {A : Set a} n {m} → Vec A (n + m) → Vec A n × Vec A m
splitV  zero        xs  = [] , xs
splitV (suc n) (x ∷ xs) = first (x ∷_) (splitV n xs)

listToBody : Vec Float 7 → Body
listToBody xs =
  case splitV 3 xs of λ where
    (ps , xs₁) →
      case splitV 3 xs₁ of λ where
        (vs , m ∷ []) → ⟨ listToPos ps , listToPos vs , m ⟩

mulL : Nat → Nat → Nat
mulL 0 _ = 0
mulL (suc n) m = m + mulL n m

bodiesToList : ∀ {n} → Vec Body n → Vec Float (mulL n 7)
bodiesToList []       = []
bodiesToList (x ∷ xs) = bodyToList x v++ bodiesToList xs

listToBodies : ∀ {n} → Vec Float (mulL n 7) → Vec Body n
listToBodies {zero} [] = []
listToBodies {suc n} xs =
  flip uncurry (splitV 7 xs) λ ys xs₁ → listToBody ys ∷ listToBodies xs₁

advance : ∀ {n} → Float → Vec Body n → Vec Body n
advance δt = fmap move ∘ go
  where
    move : Body → Body
    move ⟨ p , v , m ⟩ = ⟨ p + diag δt * v , v , m ⟩

    update : Body → Body → Body × Body
    update ⟨ p , v , m ⟩ ⟨ p₁ , v₁ , m₁ ⟩ =
      let~ u   := p - p₁ ~in
      let~ d²  := ∣ u ∣² ~in
      let~ mag := δt / (d² * sqrt d²) ~in
      ⟨ p  , v  - u * diag (m₁ * mag) , m ⟩ ,
      ⟨ p₁ , v₁ + u * diag (m  * mag) , m₁ ⟩

    updates : ∀ {n} → Body → Vec Body n → Body × Vec Body n
    updates b []        = b , []
    updates b (b₁ ∷ bs) =
      case update b b₁ of λ where
        (b′ , b₁′) → second (b₁′ ∷_) (updates b′ bs)

    go : ∀ {n} → Vec Body n → Vec Body n
    go []       = []
    go (b ∷ bs) = case updates b bs of λ where
                    (b′ , bs′) → b′ ∷ go bs′

advanceM : ∀ {n} → Float → Array (mulL n 7) → IO ⊤
advanceM {n} δt arr = onArray (bodiesToList {n} ∘ advance δt ∘ listToBodies) arr

iterateM : Nat → IO ⊤ → IO ⊤
iterateM zero _ = return _
iterateM (suc n) m = m >> iterateM n m

ptrSolution : Nat → IO ⊤
ptrSolution n = do
  putStr (printf "%.9f\n" (energy bodies))
  arr ← allocArray (bodiesToList {numBodies} bodies)
  iterateM n (static (advanceM {numBodies} 0.01 arr))
  xs ← readArray arr
  putStr (printf "%.9f\n" (energy (listToBodies {numBodies} xs)))

main : IO ⊤
main = withNatArg ptrSolution

-- Times
--         N   Time     Mem  Prod
--   100,000   3.8s  1040MB
--             0.6s    14MB        strict lets in update
-- 1,000,000   6.4s   122MB
--             6.0s   122MB        translate force to seq
--             4.1s   122MB        compile Triple to Haskell data with strict fields
--             3.7s   123MB   48%  compile Body to the same type
--             2.2s     1MB   98%  made iterate strict (duh)
--             1.9s     1MB   98%  match on p and v in update
--             1.8s                turn on some ghc optimisations
--             1.1s                specialise the Triple types (allows unboxing)
--             0.3s                backend optimisations
-- 5,000,000   1.6s

-- Array-based
-- 10,000,000  3.6s
