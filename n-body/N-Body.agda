
module N-Body where

open import Prelude hiding (Vec)
open import Builtin.Float
open import Text.Printf
open import NoFib.IO

data Triple (A : Set) : Set where
  ⟨_,_,_⟩ : (x y z : A) → Triple A

_∙_ : {A : Set} {{_ : Semiring A}} → Triple A → Triple A → A
⟨ x , y , z ⟩ ∙ ⟨ x₁ , y₁ , z₁ ⟩ = x * x₁ + y * y₁ + z * z₁

instance
  FunTriple : Functor Triple
  fmap {{FunTriple}} f ⟨ x , y , z ⟩ = ⟨ f x , f y , f z ⟩

  AppTriple : Applicative Triple
  pure {{AppTriple}} x = ⟨ x , x , x ⟩
  _<*>_ {{AppTriple}} ⟨ f , g , h ⟩ ⟨ x , y , z ⟩ = ⟨ f x , g y , h z ⟩

  SemiringTriple : {A : Set} {{_ : Semiring A}} → Semiring (Triple A)
  zro {{SemiringTriple}} = pure zro
  one {{SemiringTriple}} = pure one
  _+_ {{SemiringTriple}} u v = _+_ <$> u <*> v
  _*_ {{SemiringTriple}} u v = _*_ <$> u <*> v

  SubTriple : {A : Set} {{_ : Subtractive A}} → Subtractive (Triple A)
  negate {{SubTriple}} = fmap negate
  _-_    {{SubTriple}} u v = _-_ <$> u <*> v

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
  field
    p : Pos
    v : Vec
    m : Float

energy : List Body → Float
energy = go 0.0
  where
    go : Float → List Body → Float
    go e []       = e
    go e (b ∷ bs) = go (e + 0.5 * m * (v ∙ v) -
                        sum (for b₁ ← bs do (m * Body.m b₁) / ∣ p - Body.p b₁ ∣)) bs
      where open Body b

syntax letbind x (λ y → z) = letv y ← x do z
infix 0 letbind
letbind : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
letbind x f = f x
{-# INLINE letbind #-}

{-# TERMINATING #-}
advance : Float → List Body → List Body
advance δt = map move ∘ go
  where
    move : Body → Body
    move b = record { Body b; p = p + pure δt * v }
      where open Body b

    update : Body → Body → Body × Body
    update b₁ b₂ =
      letv u   ← b₁.p - b₂.p   do
      letv d²  ← u ∙ u         do
      letv d   ← sqrt d²       do
      letv mag ← δt / (d² * d) do
      record { b₁; v = b₁.v - u * pure (b₂.m * mag) } ,
      record { b₂; v = b₂.v + u * pure (b₁.m * mag) }
      where
        module b₁ = Body b₁
        module b₂ = Body b₂

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
