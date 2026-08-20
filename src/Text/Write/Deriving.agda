------------------------------------------------------------------------
-- The Agda standard library
--
-- Macro for deriving instances of Write
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- NOTE: still figuring things out, just pushing to get over to other device

module Text.Write.Deriving where

-- Much understanding and structure taken from
--   ∙ https://github.com/UlfNorell/agda-prelude/blob/master/src/Tactic/Deriving/Eq.agda
--   ∙ https://github.com/alhassy/gentle-intro-to-reflection

open import Data.List.Base using (_∷_; []; List; concat; _++_; zip)
open import Data.List.Effectful
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Instances using (NatWrite)
open TraversableM using (mapM)
open import Data.Unit using (⊤)
open import Data.Product.Base using (_×_; _,_; uncurry; proj₁; proj₂)
open import Reflection
open import Reflection.AST.Term using (Telescope; Clause)
open import Reflection.TCM
open import Reflection.TCM.Effectful using () renaming (monad to monadTCM)
open import Text.Write using (Write; Char; Precedence)

data Test : Set where
  a : ℕ → (x : ℕ) → ℕ → Test

{-
Should this be placed in Tactic.DerivingWrite?

For now, some notes on design:

Should print syntactically correct Agda that can be read by
an also derived Read instance.

Steps:
1. Check term is actually a data/record definition, if not throw typecheck error?
2. Get all parameters and attach required instances to the resulting function type

   only need instances for types within constructors, e.g.

   data {a : Level} {A : Set} → MyData A : Set a where
     c : A → A → MyData A

   needs to have

   {a : Level} {A : Set} {{ Write A }} → Write (List A)

   NOT

   {a : Level} {A : Set} {{ Write a }} {{ Write A }} → Write (List A)


3. For records, print in record syntax (record { x = y, ... }), recursively
   calling write on fields
4. For data, get fixity of constructor and recursively call write, intertwining
   parts of the constructors name in a way that properly aligns with fixity

   (e.g. print x ∷ [] as "x ∷ []", not "_∷_ x []")

Reflection notes:
- Prelude has a lot of machinery that should be moved over
- Should derive *own* type so we know the exact order things are in
- Instance arguments MUST be included in telescope and argument patterns, and must be provided
  to calls to writesPrecList, as opposed to say instance resolution within the definition.
  (at least I think)
- Clause takes telescope of arguments (i.e. the type of the given function without the return value)
  AND a list of patterns applied to those arguments. If no pattern matching is applied, just the
  deBruijin index within a var pattern should be given.

-}

------------------------------------------------------------------------
-- Machinery for deriving things

telView : Type → Telescope × Type
telView (pi x (abs y b)) = ((y , x) ∷ (proj₁ telVb)) , proj₂ telVb
  where
    telVb : Telescope × Type
    telVb = telView b
{-# CATCHALL #-}
telView x                = [] , x

-- Construct a Type out of a Telescope and Core Type
telToType : Telescope → Type → Type
telToType tel core = {!!}

-- Return a list of all types that appear in the constructors
-- or fields of a data or record type that aren't the type itself
-- in order of appearance
--
-- e.g. for
-- data X : Set where
--   c₁ : ℕ → X
--   c₂ : Bool → X → X
--
-- This should return ℕ, Bool
consArgTypes : Type → List Type
consArgTypes = {!!}

instanceArg : Arg Name
instanceArg = arg (arg-info instance′ defaultModality) (quote Write)

-- Derive the telescope for the type of an instance,
--
-- e.g. for Write List this returns
--      {a : Level} {A : Set a} {{ Write A }}
instanceTel : Name → Name → TC Telescope
instanceTel = {!!}

-- Derive the type of an instance for a given record type,
-- prepending all required instances to the telescope
--
-- e.g. for Write (List), will give
--      : {{ Write A }} → Write (List A)
instanceType : Name → Name → TC Type
instanceType cls inst = do
  clsT ← getType cls
  instT ← getType inst
  tel ← instanceTel cls inst
  pure (telToType tel {!!})

telStr : Telescope → List ErrorPart
telStr [] = strErr "[]" ∷ []
telStr ((nm , arg i t) ∷ xs) = strErr nm ∷ termErr t ∷ (telStr xs)

vra : {A : Set} → A → Arg A
vra = arg (arg-info visible (modality relevant quantity-0))

vrv :  ℕ → List (Arg Term) → Arg Term
vrv n args = arg (arg-info visible (modality relevant quantity-0)) (var n args)

vri : ℕ → Arg Term
vri n = arg (arg-info instance′ (modality relevant quantity-0)) (var n [])

vrv' : ℕ → Arg Term
vrv' n = vrv n []

------------------------------------------------------------------------
-- Machinery specific to Write

-- TODO: doc comment can be better
-- given the telescope for a constructor, produce the whole telescope for
-- its clause
-- Precedence → A → List Char → List Char
conTel : Telescope → Telescope
conTel tel =  ("str" , (vra (quoteTerm (List Char)))) ∷ (tel ++ ("prec" , (vra (quoteTerm Precedence))) ∷ [])

------------------------------------------------------------------------
-- Derive macro for Write

-- test implementation, no bracketing

-- concat write calls to each argument in a telescope for Write
-- suc suc N is used because we have Prec → A → List Char → List Char, so everything is one more away
-- because of the List Char taken as an argument

telWrite : ℕ → Term
telWrite ℕ.zero = con (quote List.[]) []
telWrite (ℕ.suc n) = def (quote _++_) (vra (def (quote Write.writesPrecList) (vri 5 ∷ vrv' 0 ∷ vrv' (1 + n) ∷ vrv' 4 ∷ [])) ∷ (vra (telWrite n)) ∷ [])
-- telWrite 0 = con (quote (List.[])) []
-- telWrite (suc n) = def (quote _++_) ({!!} ∷ {!!})

varPat : ℕ → Arg Pattern
varPat n = vra (Pattern.var n)

telToVarPat : ℕ → List (Arg Pattern)
telToVarPat 0 = []
telToVarPat (ℕ.suc n) = telToVarPat n ++ (varPat (1 + n)) ∷ []

-- derive the clause for a single constructor
consClause : Name → Type → Clause
consClause nm t with telView t
... | tel , _ = Clause.clause (conTel tel) (varPat 0 ∷ (vra (Pattern.con nm (telToVarPat (Data.List.Base.length tel)))) ∷ varPat 4 ∷ []) (telWrite (Data.List.Base.length tel))

deriveWriteFun : Name → Definition → Definition
deriveWriteFun nm (Reflection.data-type pars cs) = function (Data.List.Base.map (uncurry consClause) {!!})
deriveWriteFun nm (Reflection.record-type c fs) = {!!}
{-# CATCHALL #-}
deriveWriteFun _ _ = function []
-- cs in data-type contains actual constructor names
-- 'name' in data-cons is just name of data type itself
deriveWrite' : Definition → Term → TC ⊤
deriveWrite' (Reflection.record-type c fs) met = {!!}
deriveWrite' (data-type p cs) met = do
  ts ← mapM monadTCM getType cs
  let clauses = (Data.List.Base.map (uncurry consClause) (zip cs ts))
      term = telWrite 5
  typeError (termErr (pat-lam clauses []) ∷ [])
-- unify met (pat-lam clauses [])
{-# CATCHALL #-}
deriveWrite' _ _  = typeError (strErr "Write instances can only be derived for data and record types" ∷ [])

macro
  deriveWrite : Name → Term → TC ⊤
  deriveWrite nm met = do
    d ← getDefinition nm
    deriveWrite' d met
