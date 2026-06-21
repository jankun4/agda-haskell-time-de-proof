------------------------------------------------------------------------
-- Principle 4 · Struktura / Structure
--
-- From bonds, form.  Attestations are gathered into BLOCKS; blocks,
-- hash-linked, form the LEDGER — an append-only chain.  The structural
-- guarantee (history is never rewritten) is the `prefix-preserves`
-- theorem, re-exported here for blocks.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.P4_Structure where

open import Sanctum.P0_Void
open import Sanctum.P1_Truth
open import Sanctum.P3_Connection
open import Data.Nat using (ℕ)
open import Data.List using (List)

import Sanctum.Proofs.Append as A

-- A block header commits to its parent, the Merkle root of its
-- attestations, the agreed block time, and the validator-set epoch.
record BlockHeader : Set where
  constructor mkHeader
  field
    parentHash : Hash
    merkleRoot : Hash
    blockTime  : ℕ      -- the BFT-agreed median time (see P6_Harmony)
    epoch      : ℕ      -- which validator set finalised this block

open BlockHeader public

-- A block: its header plus the attestations it seals in.
record Block : Set where
  constructor mkBlock
  field
    header       : BlockHeader
    attestations : List Attestation

open Block public

-- The ledger is an append-only chain of blocks; we re-export the chain
-- machinery and the append-only theorem specialised to blocks.
module Ledger = A.AppendOnly Block

open Ledger public
  using ( Chain; genesis; _▸_; height; blockAt
        ; _≼_; refl≼; snoc≼; ≼-trans; extend-grows
        ; inject≼; prefix-preserves )
