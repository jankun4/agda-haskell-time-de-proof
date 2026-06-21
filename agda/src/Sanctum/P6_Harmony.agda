------------------------------------------------------------------------
-- Principle 6 · Doskonałość, harmonia / Perfection, Harmony
--
-- All the layers come into accord.  Two capstone theorems crown the
-- system, plus the offline proof object (Testament) and the link to the
-- total contract language.
--
--   * AGREEMENT.  Under the fault assumption, two conflicting blocks can
--     never both be finalised — distrusting hospitals converge on one
--     history.  (From quorum intersection, Principle 5.)
--
--   * TIMESTAMP SOUNDNESS.  A finalised block's time lies within the
--     honest validators' clock interval — trustworthy time with no
--     external authority.  (From the median bound, Principle 6 time.)
--
--   * TESTAMENT.  The self-contained, offline-verifiable certificate a
--     hospital hands to anyone to prove "this document existed by time T".
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.P6_Harmony where

open import Sanctum.P0_Void
open import Sanctum.P1_Truth
open import Sanctum.P2_Distinction
open import Sanctum.P3_Connection
open import Sanctum.P4_Structure
open import Sanctum.P5_Life

open import Data.Nat using (ℕ; _≤_; _+_; _*_)
open import Data.Bool using (Bool; true)
open import Data.Vec using (Vec; lookup)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Sanctum.Proofs.Counting using (count; ∁)
import Sanctum.Proofs.Quorum as Q
import Sanctum.Proofs.Time as T

------------------------------------------------------------------------
-- AGREEMENT  (safety of consensus).

module Agreement
  (vs  : ValidatorSet)
  (h   : Vec Bool (size vs))                       -- the honest validators
  (qb  : size vs + (fault vs + 1) ≤                -- quorum obligation 2q ≥ n+f+1
         quorumThreshold vs + quorumThreshold vs)  --   (holds for q=n−f when n≥3f+1)
  (d≤f : count (∁ h) ≤ fault vs)                   -- at most f dishonest
  where

  -- Any two quorums share an honest validator.
  shared-honest-signer :
    (c₁ c₂ : QuorumCert (size vs)) →
    IsQuorum vs c₁ → IsQuorum vs c₂ →
    ∃[ i ] ( lookup (signers c₁) i ≡ true
           × lookup (signers c₂) i ≡ true
           × lookup h i ≡ true )
  shared-honest-signer c₁ c₂ q₁ q₂ =
    Q.quorum-intersection-honest (fault vs)
      (signers c₁) (signers c₂) h (quorumThreshold vs) qb q₁ q₂ d≤f

  -- Consequently, given that honest validators do not equivocate (sign
  -- two different blocks at one height), two finalised blocks coincide.
  -- NOTE: no-equivocation is taken here as a hypothesis, not yet proved
  -- from a per-height voting model (see docs/limitations.md §2).
  no-two-conflicting :
    (b₁ b₂ : Block)
    (c₁ c₂ : QuorumCert (size vs)) →
    IsQuorum vs c₁ → IsQuorum vs c₂ →
    ( ∀ i → lookup h i ≡ true
          → lookup (signers c₁) i ≡ true
          → lookup (signers c₂) i ≡ true
          → b₁ ≡ b₂ ) →                            -- no-equivocation
    b₁ ≡ b₂
  no-two-conflicting b₁ b₂ c₁ c₂ q₁ q₂ honest-no-equiv
    with shared-honest-signer c₁ c₂ q₁ q₂
  ... | i , s₁ , s₂ , hon = honest-no-equiv i hon s₁ s₂

------------------------------------------------------------------------
-- TIMESTAMP SOUNDNESS  (trustworthy time without an authority).
--
-- A block's `blockTime` is the median of the quorum's clock samples.
-- If > f signers are honest with clocks in [lo,hi], the median is too.
-- NOTE: this is conditional on `IsMedian`; that the executable `medianTime`
-- produces such a value is tested, not yet proved (docs/limitations.md §2).
-- The bound is a *consistency* guarantee, not absolute time (timestamping.md).

module TimeSoundness (f : ℕ) where

  timestamp-sound :
    {lo hi m : ℕ} {n : ℕ} {ts : Vec ℕ n}
    (h : Vec Bool n) →
    n ≤ 2 * f + 1 →
    f + 1 ≤ count h →
    T.IsMedian f m ts →
    (∀ i → lookup h i ≡ true → lo ≤ lookup ts i) →
    (∀ i → lookup h i ≡ true → lookup ts i ≤ hi) →
    (lo ≤ m) × (m ≤ hi)
  timestamp-sound = T.median-bound f

------------------------------------------------------------------------
-- THE TESTAMENT  (offline-verifiable proof of existence-by-time).
--
-- What a hospital hands to a third party.  It is self-contained: with
-- only the genesis-anchored validator set, the recipient can check it
-- WITHOUT contacting the network — essential for air-gapped sites.

record Testament : Set where
  constructor testament
  field
    document   : Fact          -- the document whose existence is proven
    sealedIn   : BlockHeader   -- the block that sealed it
    blockEpoch : ValidatorSet  -- the validator set that finalised it
    cert       : QuorumCert (size blockEpoch)
                               -- the quorum certificate (signers + samples)
    quorum     : IsQuorum blockEpoch cert
    -- (the node also carries a Merkle inclusion path; modelled in the
    --  kernel.  The header's blockTime is the proven-sound timestamp.)

open Testament public

-- The time a Testament proves the document existed by.
provenTime : Testament → ℕ
provenTime t = blockTime (sealedIn t)
