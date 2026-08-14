------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for List
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Instances where

open import Data.List.Base using (List; []; _∷_; foldr)
open import Data.List.Effectful
  using (functor; applicative; applicativeZero; alternative; monad
        ; monadZero; monadPlus)
import Data.List.Effectful.Transformer as Trans
  using (functor; applicative; monad; monadT)
open import Data.List.Properties
  using (≡-dec)
open import Data.List.Literals
  using (isString)
open import Data.List.Relation.Binary.Pointwise
  using (Pointwise)
open import Data.List.Relation.Binary.Lex.NonStrict
  using (Lex-≤; ≤-isDecTotalOrder)
open import Data.Nat.Instances using (NatWrite)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses
  using (IsDecTotalOrder; IsDecEquivalence; _≈?_)
open import Text.Write

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

instance
  -- List
  listFunctor = functor
  listApplicative = applicative
  listApplicativeZero = applicativeZero
  listAlternative = alternative
  listMonad = monad
  listMonadZero = monadZero
  listMonadPlus = monadPlus
  listIsString = isString
  -- ListT
  listTFunctor = λ {f} {g} {M} {{inst}} → Trans.functor {f} {g} {M} inst
  listTApplicative = λ {f} {g} {M} {{inst}} → Trans.applicative {f} {g} {M} inst
  listTMonad = λ {f} {g} {M} {{inst}} → Trans.monad {f} {g} {M} inst
  listTMonadT = λ {f} {g} {M} {{inst}} → Trans.monadT {f} {g} {M} inst

  List-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = List A} _≡_
  List-≡-isDecEquivalence = isDecEquivalence (≡-dec _≈?_)

  List-Lex-≤-isDecTotalOrder : {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂}
                             → {{IsDecTotalOrder _≈_ _≼_}}
                             → IsDecTotalOrder (Pointwise _≈_) (Lex-≤ _≈_ _≼_)
  List-Lex-≤-isDecTotalOrder {{≼-isDecTotalOrder}} = ≤-isDecTotalOrder ≼-isDecTotalOrder

------------------------------------------------------------------------
-- List write

open Write {{...}}

instance
  ListWrite : {{ Write A }} → Write (List A)
  ListWrite .writesPrecList prec [] str = '[' ∷ (']' ∷ str)
  ListWrite .writesPrecList prec (x ∷ xs) str = '[' ∷ writesPrecList prec x (listWrite' prec str xs)
    where
      -- after the first call, don't prepend '['
      listWrite' : {{ Write A }} → Precedence → List Char → List A → List Char
      listWrite' prec str = foldr (λ x str → ',' ∷ writesPrecList prec x str) (']' ∷ str)

-- some examples to write the instances working
private
  test[ℕ] : String
  test[ℕ] = write (5 ∷ 2 ∷ 12 ∷ 42 ∷ [])
