
module N-Body where

open import Prelude hiding (Vec)
open import Builtin.Float
open import Text.Printf
open import NoFib.IO

data Triple (A : Set) : Set where
  ⟨_,_,_⟩ : (x y z : A) → Triple A

{-# IMPORT NBodyPrim #-}
{-# COMPILED_DATA Triple NBodyPrim.Triple NBodyPrim.Triple #-}

_∙_ : {A : Set} {{_ : Semiring A}} → Triple A → Triple A → A
⟨ x , y , z ⟩ ∙ ⟨ x₁ , y₁ , z₁ ⟩ = x * x₁ + y * y₁ + z * z₁

pureT : {A : Set} → A → Triple A
pureT x = ⟨ x , x , x ⟩
{-# INLINE pureT #-}

appT : {A B : Set} → Triple (A → B) → Triple A → Triple B
appT ⟨ f , g , h ⟩ ⟨ x , y , z ⟩ = ⟨ f x , g y , h z ⟩
{-# INLINE appT #-}

mapT : {A B : Set} → (A → B) → Triple A → Triple B
mapT f x = appT (pureT f) x
{-# INLINE mapT #-}

η : {A B : Set} → Triple A → (Triple A → B) → B
η ⟨ x , y , z ⟩ f = f ⟨ x , y , z ⟩
{-# INLINE η #-}

η₂ : {A B C : Set} → Triple A → Triple B → (Triple A → Triple B → C) → C
η₂ ⟨ x , y , z ⟩ ⟨ x₁ , y₁ , z₁ ⟩ f = f ⟨ x , y , z ⟩ ⟨ x₁ , y₁ , z₁ ⟩
{-# INLINE η₂ #-}

instance
  FunTriple : Functor Triple
  fmap {{FunTriple}} = mapT

  AppTriple : Applicative Triple
  pure {{AppTriple}} = pureT
  _<*>_ {{AppTriple}} = appT

  SemiringTriple : Semiring (Triple Float)
  zro {{SemiringTriple}} = pure zro
  one {{SemiringTriple}} = pure one
  _+_ {{SemiringTriple}} u v = η₂ u v λ u v → _+_ <$> u <*> v
  _*_ {{SemiringTriple}} u v = η₂ u v λ u v → _*_ <$> u <*> v

  SubTriple : Subtractive (Triple Float)
  negate {{SubTriple}} = fmap negate
  _-_    {{SubTriple}} u v = η₂ u v λ u v → _-_ <$> u <*> v

  FracTriple : Fractional (Triple Float)
  Fractional.Constraint FracTriple _ _ = ⊤
  _/_ {{FracTriple}} u v = (λ x y → x / y) <$> u <*> v

Pos = Triple Float
Vec = Pos

∣_∣ : Vec → Float
∣ v ∣ = sqrt (v ∙ v)

daysPerYear : Float
daysPerYear = 365.24

solarMass : Float
solarMass = 4 * π ^ 2

record Body : Set where
  no-eta-equality
  constructor ⟨_,_,_⟩
  field
    p : Pos
    v : Vec
    m : Float

{-# COMPILED_DATA Body NBodyPrim.Body NBodyPrim.Triple #-}

energy : List Body → Float
energy = go 0.0
  where
    go : Float → List Body → Float
    go e []       = e
    go e (b ∷ bs) = go (e + 0.5 * m * (v ∙ v) -
                        sum (for b₁ ← bs do (m * Body.m b₁) / ∣ p - Body.p b₁ ∣)) bs
      where open Body b

infix 0 letstrict
syntax letstrict x (λ y → z) = let! y ← x do z
letstrict : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
letstrict x f = force x f
-- {-# INLINE letstrict #-} -- makes it 15% slower!

{-# TERMINATING #-}
advance : Float → List Body → List Body
advance δt = map move ∘ go
  where
    move : Body → Body
    move b = record { Body b; p = p + pure δt * v }
      where open Body b

    update : Body → Body → Body × Body
    update ⟨ p , v , m ⟩ ⟨ p₁ , v₁ , m₁ ⟩ =
      let! u   ← p - p₁        do
      let! d²  ← u ∙ u         do
      let! d   ← sqrt d²       do
      let! mag ← δt / (d² * d) do
      ⟨ p  , v - u * pure (m₁ * mag) , m ⟩ ,
      ⟨ p₁ , v₁ + u * pure (m * mag) , m₁ ⟩

    updates : Body → List Body → Body × List Body
    updates b []        = b , []
    updates b (b₁ ∷ bs) =
      case update b b₁ of λ
      { (b′ , b₁′) → second (b₁′ ∷_) (updates b′ bs) }

    go : List Body → List Body
    go []       = []
    go (b ∷ bs) = case updates b bs of λ { (b′ , bs′) → b′ ∷ go bs′ }

-- Planets --

jupiter : Body
Body.p jupiter = ⟨ 4.84143144246472090 , -1.16032004402742839 , -1.03622044471123109e-01 ⟩
Body.v jupiter = ⟨ 1.66007664274403694e-03 , 7.69901118419740425e-03 , -6.90460016972063023e-05 ⟩ * pure daysPerYear
Body.m jupiter = 9.54791938424326609e-04 * solarMass

saturn : Body
Body.p saturn = ⟨ 8.34336671824457987e+00 ,  4.12479856412430479e+00 , -4.03523417114321381e-01 ⟩
Body.v saturn = ⟨ -2.76742510726862411e-03 ,  4.99852801234917238e-03 ,  2.30417297573763929e-05 ⟩ * pure daysPerYear
Body.m saturn = 2.85885980666130812e-04 * solarMass

uranus : Body
Body.p uranus = ⟨ 1.28943695621391310e+01 , -1.51111514016986312e+01 , -2.23307578892655734e-01 ⟩
Body.v uranus = ⟨ 2.96460137564761618e-03 ,  2.37847173959480950e-03 , -2.96589568540237556e-05 ⟩ * pure daysPerYear
Body.m uranus = 4.36624404335156298e-05 * solarMass

neptune : Body
Body.p neptune = ⟨ 1.53796971148509165e+01 , -2.59193146099879641e+01 , 1.79258772950371181e-01 ⟩
Body.v neptune = ⟨ 2.68067772490389322e-03 ,  1.62824170038242295e-03 , -9.51592254519715870e-05 ⟩ * pure daysPerYear
Body.m neptune = 5.15138902046611451e-05 * solarMass

sun : Body
Body.p sun = pure 0
Body.v sun = pure 0
Body.m sun = solarMass

offsetMomentum : Pos → Body → Body
offsetMomentum p b = record { Body b; v = negate (p / pure solarMass) }

bodies : List Body
bodies = offsetMomentum p sun ∷ planets
  where
    planets : List Body
    planets = jupiter ∷ saturn ∷ uranus ∷ neptune ∷ []
    p : Pos
    p = sum (map (λ b →  Body.v b * pure (Body.m b)) (sun ∷ planets))

iterate : ∀ {a} {A : Set a} → Nat → (A → A) → A → A
iterate zero    _ x = x
iterate (suc n) f x = iterate n f (f x)

main : IO ⊤
main = withNatArg λ n →
  putStr (printf "%.9f\n" (energy bodies)) >>
  putStr (printf "%.9f\n" (energy (iterate n (advance 0.01) bodies)))

-- Times
--         N   Time     Mem  Prod
--   100,000   3.8s  1040MB
--             0.6s    14MB        strict lets in update
-- 1,000,000   6.4s   122MB
--             6.0s   122MB        translate force to seq
--             4.1s   122MB        compile Triple to Haskell data with strict fields
--             3.7s   123MB   48%  compile Body to the same type
