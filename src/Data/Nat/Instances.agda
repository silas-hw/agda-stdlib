------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Instances where

open import Data.List.Base using (_++_)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤-isDecTotalOrder; _≡?_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Text.Write using (Write)

instance
  ℕ-≡-isDecEquivalence = isDecEquivalence _≡?_
  ℕ-≤-isDecTotalOrder = ≤-isDecTotalOrder

instance
  open Write
  NatWrite : Write ℕ
  NatWrite .writesPrecList _ n str = (toList (showℕ n)) ++ str
