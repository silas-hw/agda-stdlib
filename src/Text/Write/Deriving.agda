------------------------------------------------------------------------
-- The Agda standard library
--
-- Macro for deriving instances of Write
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Write.Deriving where

open import Data.List.Base using (_∷_; []; List; concat; _++_; zip)
open import Data.List.Effectful
open import Data.Nat.Base using (ℕ)
open TraversableM using (mapM)
open import Data.Unit using (⊤)
open import Data.Product.Base using (_×_; _,_; uncurry; proj₁; proj₂)
open import Reflection
open import Reflection.AST.Term using (Telescope; Clause)
open import Reflection.TCM.Effectful using () renaming (monad to monadTCM)
open import Text.Write

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

Reflection notes:
- Prelude has a lot of machinery that should be moved over
- Should derive *own* type so we know the exact order things are in
-}

------------------------------------------------------------------------
-- Machinery for deriving things

-- Derive the type of an instance for a given record type
instanceArg : Arg Name
instanceArg = arg (arg-info instance′ defaultModality) (quote Write)

instanceType : Name → Name → TC Type
instanceType = {!!}

telView : Type → Telescope × Type
telView (pi a (abs x b)) = ((x , a) ∷ (proj₁ telVb)) , proj₂ telVb
  where
    telVb : Telescope × Type
    telVb = telView b
telView a                = [] , a


telStr : Telescope → List ErrorPart
telStr [] = strErr "" ∷ []
telStr ((nm , arg i t) ∷ xs) = strErr nm ∷ termErr t ∷ (telStr xs)

------------------------------------------------------------------------
-- Actual derive tactic for Write

-- test implementation, no bracketing

defStr : Definition → List ErrorPart
defStr (function cs) = (strErr "function") ∷ []
defStr (data-type pars cs) = (strErr "data-type") ∷ []
defStr (record-type c fs) = (strErr "record-type") ∷ []
defStr (data-cons d q) = strErr "data-cons" ∷ (nameErr d) ∷ []
defStr axiom = (strErr "axiom") ∷ []
defStr prim-fun = (strErr "prim-fun") ∷ []

nameStr : (Name × Type) → List ErrorPart
nameStr (nm , t) = (nameErr nm) ∷ (strErr " : ") ∷ (telStr (proj₁ (telView t)))

vra : {A : Set} → A → Arg A
vra = arg (arg-info visible (modality relevant quantity-0))

vrv :  ℕ → List (Arg Term) → Arg Term
vrv n args = arg (arg-info visible (modality relevant quantity-0)) (var n args)

-- concat write calls to each argument in a telescope
open Write
telWrite : ℕ → Term
telWrite ℕ.zero = con (quote List.[]) []
telWrite (ℕ.suc n) = def (quote _++_) (vra (def (quote write) ((vrv (ℕ.suc n) []) ∷ [])) ∷ (vra (telWrite n)) ∷ [])
-- telWrite 0 = con (quote (List.[])) []
-- telWrite (suc n) = def (quote _++_) ({!!} ∷ {!!})

-- derive the clause for a single constructor
consClause : Name → Type → Clause
consClause nm t with telView t
... | tel , _ = Clause.clause tel [] (telWrite (Data.List.Base.length tel))

deriveWriteFun : Name → Definition → Clause
deriveWriteFun nm (Reflection.data-type pars cs) = {!!}
deriveWriteFun nm (Reflection.record-type c fs) = {!!}
deriveWriteFun _ _ = Clause.absurd-clause [] []

-- cs in data-type contains actual constructor names
-- 'name' in data-cons is just name of data type itself
deriveWrite' : Definition → Term → TC ⊤
deriveWrite' (Reflection.record-type c fs) met = {!!}
deriveWrite' (data-type p cs) met = do
  ts ← mapM monadTCM getType cs
  let clauses = (Data.List.Base.map (uncurry consClause) (zip cs ts))
      errs    = concat (Data.List.Base.map nameStr (zip cs ts))
  let term = telWrite 5
  {!!}
  typeError errs
deriveWrite' _ _ = typeError (strErr "Write instances can only be derived for data and record types" ∷ [])

macro
  deriveWrite : Name → Term → TC ⊤
  deriveWrite nm met = do
    d ← getDefinition nm
    deriveWrite' d met

data Test : Set where
  a : ℕ → (a : ℕ) → ℕ → Test
