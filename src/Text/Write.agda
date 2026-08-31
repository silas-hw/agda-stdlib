------------------------------------------------------------------------
-- The Agda standard library
--
-- Write class
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe  #-}

module Text.Write where

-- should builtin be used?
open import Data.Bool.Base using (true; false)
open import Data.Char.Base using (Char) public
open import Data.List.Base using (List; []; [_]; _++_; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (String) public
open import Data.String.Base using (fromList; toList)
open import Function.Base using (_∘_; const; _$_)
open import Level using (Level)
open import Reflection.AST.Fixity

private
  variable
    a : Level
    A : Set a

record Write (A : Set a) :  Set a where
  constructor mkWrite
  field
    writesPrecList :  Precedence → A → List Char → List Char

  writePrecList : Precedence → A → List Char
  writePrecList prec x =  writesPrecList prec x []

  writesPrec : Precedence → A → String → String
  writesPrec prec x str = fromList (writesPrecList prec x (toList str))

  writePrec : Precedence → A → String
  writePrec prec x = fromList (writesPrecList prec x [])

  write : A → String
  write = writePrec Precedence.unrelated

  writeMaybe : Maybe A → String
  writeMaybe nothing = ""
  writeMaybe (just x) = write x

------------------------------------------------------------------------
-- Utils

-- surround a string with two given characters (e.g. parentheses) if
-- the string represents the result of calling `write` on an inner
-- operator/function whose precedence is lower than or equal to
-- the calling operator/function
writeSurround : Char → Char → Precedence → Precedence → List Char → List Char
writeSurround lbrac rbrac callerPrec calleePrec str with (calleePrec ≤ᵇ callerPrec)
... | false = str
... | true = lbrac ∷ (str ++ [ rbrac ])

writeParens : Precedence → Precedence → List Char → List Char
writeParens = writeSurround '(' ')'
