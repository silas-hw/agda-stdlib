
open import Data.Maybe.Base
open import Text.Pretty 80
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

open Pretty {{...}}
instance
  MaybePretty : {{ Pretty A }} → Pretty (Maybe A)
  MaybePretty .pPrintPrec prec (just x) = (text "just") <+> pPrintPrec prec x
  MaybePretty .pPrintPrec prec nothing = text "nothing"
