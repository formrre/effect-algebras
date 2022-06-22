module NegativeResults.Free where

{-# NO_POSITIVITY_CHECK #-}
data Free (F : Set -> Set) : Set -> Set where
  Pure   : forall {A} -> Free F A
  Impure : forall {A} -> F (Free F A) -> Free F A
