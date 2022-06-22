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
-- constructors. Section 2 shows how this comes out as a failure to
-- have all colimits in type theory.

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
intialAlgebraChainHomom : (F : Set -> Set) (fmap : Fmap F)
 -> forall {i j : ℕ} {prf : i < j}
 -> initialAlgebraChain F i -> initialAlgebraChain F j
intialAlgebraChainHomom F fmap {zero} {zero} {()}
intialAlgebraChainHomom F fmap {zero} {suc zero} {s≤s z≤n} = λ ()
intialAlgebraChainHomom F fmap {suc i} {suc j} {s≤s prf} = fmap (intialAlgebraChainHomom F fmap {i} {j} {prf})

-- This chain has a colimit:
-- i.e., W 0 + (W 1 + (W 2 + ...)))
-- i.e., 0 + (F + (F .F + ...))
-- but it is NOT (WELL-)DEFINED IN TYPE THEORY which is the problem
{-# TERMINATING #-}
colimitChain : (W : ℕ -> Set) -> Set
colimitChain W = W 0 ⊎ colimitChain (\x -> W (suc x))

postulate
  prf : {F : Set -> Set}
    -> colimitChain (\x -> F (initialAlgebraChain F x))
       ≡ F (colimitChain (initialAlgebraChain F))

-- Injections into the colimit of our initial algebra chain
colimitInj : {F : Set -> Set} {fmap : Fmap F} {i : ℕ}
  -> initialAlgebraChain F i -> colimitChain (initialAlgebraChain F)
colimitInj {F} {fmap} {zero} x = inj₁ x
colimitInj {F} {fmap} {suc i} x rewrite prf {F} =
  inj₂ (fmap (colimitInj {F} {fmap} {i}) x)

isColimit : {F : Set -> Set} {fmap : Fmap F} {i j : ℕ} {prf : i < j}
          -> (x : F i)
          -> colimitInj {F} {fmap} {i} x
          ≡ colimitInj {F} {fmap} {j} (intialAlgebraChainHomom {i} {j} {prf} x)
isColimit {F} {i} {j} {prf} x = ?
