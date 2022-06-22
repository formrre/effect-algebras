module Freer.Base where
{-

  Defines the key data types for the "freer monad" construction.
  Properties are given in Freer.Properties.

-}

open import Agda.Primitive
open import Level
open import Data.Product

-- Left-Kan extension of a type constructor

Lan : {l1 l2 l3 : _} → (G : Set l1 → Set l2) → (A : Set l3) → Set (lsuc l1 ⊔ l2 ⊔ l3)
Lan {l1} {l2} G A = Σ (Set l1) λ X → G X × (X → A)

-- Freer representation of free monads via Left-Kan extension

data Freer {l1 l2 l3 : _} (G : Set l1 → Set l2) (A : Set l3) : Set (lsuc l1 ⊔ l2 ⊔ l3) where
   Pure   : A → Freer G A
   Impure : Lan G (Freer G A) → Freer G A

-- 'Iteration principle', i.e., how to fold a syntax tree

interpret : ∀ {l1 l3} {E : Set l1 -> Set l3} {x : Set (lsuc l1)} → (Lan E x → x) → (Freer E x → x)
interpret f (Pure x) = x
interpret f (Impure (type , arg , kont)) = f (type , arg , λ z → interpret f (kont z))
