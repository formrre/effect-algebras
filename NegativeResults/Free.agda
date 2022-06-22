module NegativeResults.Free where

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Nat

-- # 0. Prolog

-- The free monad cannot be defined in type theory,
-- unless we turn off the positivity check.

{-# NO_POSITIVITY_CHECK #-}
data Free (F : Set -> Set) : Set -> Set where
  Pure   : forall {A} -> Free F A
  Impure : forall {A} -> F (Free F A) -> Free F A

-- Turning off the positivity check leads to inconsistency:
-- essentially this definition is not allowed to work in general.

-- Section 1 shows how inconsistency falls out from this construction,
-- but first splitting it into a general fixed point on type
-- constructors. Section 2 shows how this failure to define Free is
-- a consequence of the fact that in type theory we do not have all
-- colimits: we cannot define the colimit of an initial algebra chain
-- formed from repeated application of a constructor to itself.

-- # 1. From general fixed point to inconsistenvy

-- Boilerplate: a notion of isomorphisms
record Iso (X : Set) (Y : Set) : Set where
  field
    embed   : X -> Y
    retract : Y -> X
    iso     : forall {x : X} -> retract (embed x) ≡ x
    isoI    : forall {y : Y} -> embed (retract y) ≡ y

open Iso

-- Fixed point over constructors
{-# NO_POSITIVITY_CHECK #-}
data Fix (F : Set -> Set) : Set where
  FixF : F (Fix F) -> Fix F

unfixF : {F : Set -> Set} -> Fix F -> F (Fix F)
unfixF (FixF f) = f

-- The free monad can then be defined in terms of this.
Free' : (Set -> Set) -> Set -> Set
Free' F A = Fix (\X -> A ⊎ F X)

-- Proof that Fix provides a fixed point
isFixedPoint : (F : Set -> Set) -> Σ Set (\X -> (Iso (F X) X))
isFixedPoint F = (Fix F ,
  record { embed = FixF ;
           retract = unfixF ;
           iso = refl ;
           isoI = isoIprop })
  where
    isoIprop : {F : Set -> Set} {y : Fix F} -> FixF (unfixF y) ≡ y
    isoIprop {F} {y} with y
    ... | FixF x = refl

-- However, this is inconsistent in type theory (as a result of
-- the NO_POSITIVITY_CHECK
bad : ⊥
bad = mkBottom (FixF mkBottom)
 where
   mkBottom : Fix (λ x → x -> ⊥) -> ⊥
   mkBottom (FixF f) = f (FixF f)

-- # 2. Colimit construction

-- (Strong) endofunctors have the `fmap` operation of type:
Fmap : (F : Set -> Set) -> Set₁
Fmap F = ∀ {A B : Set} -> (A -> B) -> F A -> F B

-- From an endofunctor we can construct the following chain:
initialAlgebraChain : (F : Set -> Set) -> ℕ -> Set
initialAlgebraChain F 0 = ⊥
initialAlgebraChain F (suc n) =
  F (initialAlgebraChain F n)

-- with maps
intialAlgebraChainHomom : (F : Set -> Set) {fmap : Fmap F}
 -> (i j : ℕ) -> {prf : i < j}
 -> initialAlgebraChain F i -> initialAlgebraChain F j
intialAlgebraChainHomom F {fmap} zero zero {()}
intialAlgebraChainHomom F {fmap} zero (suc zero) {s≤s z≤n} = λ ()
intialAlgebraChainHomom F {fmap} (suc i) (suc j) {s≤s prf} = fmap (intialAlgebraChainHomom F {fmap} i j {prf})

initialAlgebraCarrier : (F : Set -> Set) -> Set
initialAlgebraCarrier F = Σ ℕ (initialAlgebraChain F)

-- See section 6.3 of https://core.ac.uk/download/pdf/141471082.pdf
-- For an F-algebra `(Y, ρ : F Y -> Y)` there is a colimit
-- from the chain on F to Y
colimitInj : (F : Set -> Set) {fmap : Fmap F}
          -> (Y : Set)        -- Algebra carrier
          -> (ρ : F Y -> Y)   -- Algebra structure map
          -> (i : ℕ)
          -> initialAlgebraChain F i -> Y
colimitInj F {fmap} Y ρ zero    ()
colimitInj F {fmap} Y ρ (suc i) x = ρ (fmap (colimitInj F {fmap} Y ρ i) x)

refl≤ : forall {i} -> i Data.Nat.≤ i
refl≤ {zero} = z≤n
refl≤ {suc i} = s≤s refl≤

-- Proof that the above really is a colimit (i.e., we have a family of co-cones)
isColimit : (F : Set -> Set) {fmap : Fmap F} (i : ℕ)
          -> (Y : Set) (ρ : F Y -> Y) -- Algebra
          -> (x : initialAlgebraChain F i)
          -> colimitInj F {fmap} Y ρ i x
          ≡ colimitInj F {fmap} Y ρ (suc i) (intialAlgebraChainHomom F {fmap} i (suc i) {s≤s refl≤} x)
isColimit F {fmap} zero Y ρ ()
isColimit F {fmap} (suc i) Y ρ x = {!!} -- Not sure how to prove this.
