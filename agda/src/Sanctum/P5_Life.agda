------------------------------------------------------------------------
-- Principle 5 · Życie, bunt, opór / Life, Rebellion, Resistance
--
-- The structure comes alive: it defends itself against the Byzantine
-- (rebellion / resistance) and it grows (life — new hospitals join).
--
--   * RESISTANCE: a block is final only with a quorum certificate of
--     ≥ n−f validators (the classic 2f+1 at n=3f+1).  Quorum intersection
--     (Principle 5 proof) then guarantees no two conflicting blocks can
--     both be final.
--
--   * LIFE / GROWTH: the validator set evolves.  A new set is adopted
--     only when a quorum of the current set approves it, so authority
--     descends unbroken from genesis (reconfiguration safety).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.P5_Life where

open import Sanctum.P0_Void
open import Sanctum.P2_Distinction
open import Data.Nat using (ℕ; _≤_; _∸_)
open import Data.Bool using (Bool)
open import Data.Vec using (Vec)

open import Sanctum.Proofs.Counting using (count)
import Sanctum.Proofs.Quorum as Q
import Sanctum.Proofs.Append as A

-- A validator set: `size` members, tolerating `fault` Byzantine faults
-- (well-formed when size ≤ 3·fault+1, enforced by the node on adoption).
record ValidatorSet : Set where
  constructor vset
  field
    size    : ℕ
    fault   : ℕ
    members : Vec Identity size

open ValidatorSet public

-- A quorum certificate over an n-member set: which validators signed,
-- and the clock sample each contributed (used for the median time).
record QuorumCert (n : ℕ) : Set where
  constructor qc
  field
    signers : Vec Bool n   -- characteristic vector of signatories
    samples : Vec ℕ n      -- their clock readings

open QuorumCert public

-- A quorum needs "all but f" signatures: at least  n − f  of the n
-- members.  At n = 3f+1 this is the classic 2f+1; for n > 3f+1 it scales
-- so that quorum intersection still yields an honest validator (see
-- `Sanctum.Proofs.Quorum`, whose obligation 2q ≥ n+f+1 holds for q = n−f
-- exactly when n ≥ 3f+1).
quorumThreshold : ValidatorSet → ℕ
quorumThreshold vs = size vs ∸ fault vs

IsQuorum : (vs : ValidatorSet) → QuorumCert (size vs) → Set
IsQuorum vs c = quorumThreshold vs ≤ count (signers c)

-- Re-export the resistance theorem.
open Q public using (quorum-intersection-honest)

------------------------------------------------------------------------
-- Growth: a reconfiguration is approved when a quorum of the *current*
-- set certifies the next set.

record Approves (old new : ValidatorSet) : Set where
  constructor approves
  field
    cert    : QuorumCert (size old)
    quorum  : IsQuorum old cert

open Approves public

-- Authority lineage from a chosen genesis validator set.
module Growth (genesisV : ValidatorSet) where
  open A.Reconfiguration ValidatorSet genesisV Approves public
    using (Authorised; gen; step; Lineage; root; link
          ; authorised→lineage; generation)
