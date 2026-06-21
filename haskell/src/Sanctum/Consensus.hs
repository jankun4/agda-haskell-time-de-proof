-- | Principle 5 (Life/Resistance): one round of BFT finalisation.
--
-- Validators vote on a proposed block: each contributes a clock sample
-- and (if willing) a signature over the final header.  The block time is
-- the MEDIAN of the samples — so a Byzantine minority cannot move it
-- (proved: Sanctum.Proofs.Time).  The block is finalised iff ≥ n−f
-- members sign (proved safe: Sanctum.Proofs.Quorum).
module Sanctum.Consensus
  ( Vote(..)
  , finalise
  ) where

import           Sanctum.Crypto
import           Sanctum.Core   (medianTime, quorumReached)
import           Sanctum.Ledger
import           Sanctum.Types

-- | A validator's contribution to a round.
data Vote = Vote
  { voteId    :: Identity   -- which validator
  , voteSk    :: SecretKey  -- its signing key (held locally on its node)
  , voteClock :: Integer    -- the time it observes
  , voteSign  :: Bool       -- whether it endorses the block
  } deriving (Show)

-- | Finalise a block from a set of votes.  Returns the extended chain,
--   the new block, and its quorum certificate — or an error if no quorum.
finalise
  :: Integer        -- ^ maxSkew: tolerated spread of endorser clocks / claimed times
  -> ValidatorSet
  -> Int            -- ^ epoch (index of this validator set)
  -> Chain
  -> [Attestation]  -- ^ payload sealed into the block
  -> [Vote]
  -> Either String (Chain, Block, QuorumCert)
finalise maxSkew vs epoch chain payload votes
  | not (wellFormedVSet vs) =
      Left "validator set is malformed (distinct members & n >= 3f+1 required)"
  | any (\a -> abs (attClaimedTime a - blockTime) > maxSkew) payload =
      -- Bind each attestation's self-reported time to the BFT-agreed median
      -- (which a Byzantine minority cannot move): an author cannot back/post-
      -- date a document beyond maxSkew of consensus time.  (We do NOT bound
      -- the spread of raw votes — that would let one Byzantine outlier DoS the
      -- round; the median already tolerates outliers.  The NTP attack on the
      -- honest majority's shared clock is out-of-protocol — see timestamping.md.)
      Left "an attestation's claimed time is outside the agreed median window"
  | otherwise =
  let mroot      = merkleRoot (map attestationLeaf payload)
      header     = BlockHeader
                     { hdrParent     = headHash chain
                     , hdrMerkleRoot = mroot
                     , hdrBlockTime  = blockTime
                     , hdrEpoch      = epoch
                     }
      hh         = headerHash header
      sigs       = [ (voteId v, sign (voteSk v) hh) | v <- endorsers ]
      signersVec = [ m `elem` map voteId endorsers | m <- vsetMembers vs ]
      cert       = QuorumCert
                     { qcSigners    = signersVec
                     , qcSamples    = samples
                     , qcSignatures = sigs
                     }
      block      = Block header payload
  in if not (quorumReached (validatorCount vs) (faultBudget vs) signersVec)
       then Left "no quorum: fewer than n-f validators endorsed the block"
       else (\c -> (c, block, cert)) <$> appendBlock chain block
  where
    endorsers = filter voteSign votes
    samples   = map voteClock endorsers
    blockTime = medianTime samples
