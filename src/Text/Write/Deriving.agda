------------------------------------------------------------------------
-- The Agda standard library
--
-- Macro for deriving instances of Write
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Write.Deriving where

{-
Should this be placed in Tactic.DerivingWrite?

For now, some notes on design:

Should print syntactically correct Agda that can be read by
an also derived Read instance.

Steps:
1. Check term is actually a data/record definition, if not throw typecheck error?
2. Get all parameters and attach required instances to the resulting function type

   e.g. for something like

   data MyData (A : Set) : Set where
     ...

   we would need

   MyDataWrite : {A : Set} → {{ Write A }} → Write (MyData A)

   but for somethin like

   dat MyData' (x : ℕ) : Set where
     ...

   we instead need

   MyData'Write : {{ Write ℕ }} → {x : ℕ} → Write (MyData x)
3. For records, print in record syntax (record { x = y, ... }), recursively
   calling write on fields
4. For data, get fixity of constructor and recursively call write, intertwining
   parts of the constructors name in a way that properly aligns with fixity

   (e.g. print x ∷ [] as "x ∷ []", not "_∷_ x []")
-}
