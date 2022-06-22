module Main where

open import Data.Product

-- Core construction and its properties
open import Freer.Base
open import Freer.Properties

-- Required for the examples
open import Data.Empty
open import Data.Nat

-- # Motivating examples

-- ## 1. Exceptions

-- Signature of exception operations

data Exception : Set -> Set where
  Throw : Exception ⊥

-- Syntax tree of a computation which fails and then returns 0.

exampleA1 : Freer Exception ℕ
exampleA1 = Impure (⊥ , Throw , (\_ -> Pure 0))

-- A standard interpretation  for this would mean that the  0 is never
-- output.

open import Data.Maybe


-- Example reasoning principle
--
-- deadCodeTransformation : forall {k k'}
--                      -> interp (Impure (⊥ , Throw , k)) ≡ interp (Impure (⊥ , Throw , k'))



-- ## 2. State
