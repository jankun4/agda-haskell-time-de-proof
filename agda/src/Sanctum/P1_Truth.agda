------------------------------------------------------------------------
-- Principle 1 · Prawda, byt / Truth, Being
--
-- That which IS.  The atomic being of the system is a Fact: the claim,
-- witnessed by a digest, that some document exists.  A document's being
-- is its hash.  Truth here is decidable — two facts are recognisably the
-- same fact or not.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.P1_Truth where

open import Sanctum.P0_Void
open import Data.Nat using (ℕ; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

-- A Fact: the existence of a document, witnessed by its digest.
record Fact : Set where
  constructor fact
  field digest : Hash

open Fact public

-- Equality of facts is decidable (truth is recognisable).
_≟ᶠ_ : (x y : Fact) → Dec (x ≡ y)
fact d ≟ᶠ fact e with d ≟ e
... | yes refl = yes refl
... | no  d≢e  = no λ eq → d≢e (cong digest eq)
