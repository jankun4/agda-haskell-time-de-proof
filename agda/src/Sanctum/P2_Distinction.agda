------------------------------------------------------------------------
-- Principle 2 · Rozdzielenie, rozróżnienie / Separation, Distinction
--
-- To know a being is to distinguish it from another.  Here distinction
-- is IDENTITY: each hospital / node holds a key pair, and a signature
-- distinguishes the true author of a fact from a forger.
--
-- The cryptographic verifier is modelled as an abstract relation
-- `Signed pk h` ("the holder of pk signed digest h").  Its security
-- assumptions (correctness + unforgeability) are documented in
-- docs/threat-model.md and are honoured by the Ed25519 backend in the
-- Haskell node.  We reason about the protocol on top of this interface.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.P2_Distinction where

open import Sanctum.P0_Void
open import Sanctum.P1_Truth
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Relation.Nullary using (Dec; yes; no)

-- A public identity (a hospital's verifying key), an opaque identifier.
Identity : Set
Identity = ℕ

-- Distinct identities are decidably distinct.
_≟ⁱ_ : (x y : Identity) → Dec (x ≡ y)
_≟ⁱ_ = _≟_

-- A signature value.
record Sig : Set where
  constructor sig
  field bytes : Hash

open Sig public

-- The abstract verifier: `Verifies k h s` means signature s by identity
-- k attests digest h.  Decidable, because the node can check it.
record Crypto : Set₁ where
  field
    Verifies : Identity → Hash → Sig → Set
    verify?  : (k : Identity) (h : Hash) (s : Sig) → Dec (Verifies k h s)
    -- Unforgeability (stated; discharged cryptographically, not here):
    -- only the holder of k's secret key can make Verifies k h s hold for
    -- a fresh h.  Captured operationally in the node's threat model.
