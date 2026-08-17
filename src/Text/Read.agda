------------------------------------------------------------------------
-- The Agda standard library
--
-- Read class
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe  #-}

module Text.Read where

-- should builtin be used?
open import Agda.Builtin.Reflection using (Precedence) public
open import Data.Char.Base using (Char) public
open import Data.List.Base using (List; []; _++_; _∷_)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (String) public
open import Data.String.Base using (fromList; toList)
open import Function.Base using (_∘_; const; _$_)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

record Read (A : Set a) : Set a where
  field
    read : String → Maybe A
