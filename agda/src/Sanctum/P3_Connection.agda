------------------------------------------------------------------------
-- Principle 3 · Połączenie / Connection
--
-- Beings, once distinguished, are bound together.  Two kinds of bond:
--
--   * an ATTESTATION binds author ↔ fact ↔ claimed time by a signature
--     (the hospital says "I, at time t, attest this document exists");
--   * a LINK binds a block to its parent by hash, forming the chain.
--
-- Connection is what turns isolated facts into evidence and isolated
-- blocks into history.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.P3_Connection where

open import Sanctum.P0_Void
open import Sanctum.P1_Truth
open import Sanctum.P2_Distinction
open import Data.Nat using (ℕ; _+_)

-- A hospital's timestamped, signed attestation that a document exists.
record Attestation : Set where
  constructor attest
  field
    author      : Identity   -- who attests
    document    : Fact        -- what document
    claimedTime : ℕ          -- when the author claims to have signed
    signature   : Sig        -- the binding proof

open Attestation public

-- The payload an attestation's signature must cover: author ‖ digest ‖
-- time.  The committed digest depends on ALL THREE fields, matching the
-- Haskell node's `Sanctum.Crypto.attestationDigest` (which is a
-- collision-resistant hash of their canonical encoding; here the model
-- combines them with +, since Hash is an opaque ℕ).
attestationDigest : Attestation → Hash
attestationDigest a = author a + digest (document a) + claimedTime a
