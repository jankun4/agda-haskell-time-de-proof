-- | Principle 5 (Life/Resistance): one round of BFT finalisation.
--
-- Validators vote on a proposed block: each contributes a clock sample
-- and (if willing) a signature over the final header.  The block time is
-- the MEDIAN of the samples — so a Byzantine minority cannot move it
-- (proved: Sanctum.Proofs.Time).  The block is finalised iff ≥ 2f+1
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
  :: ValidatorSet
  -> Int            -- ^ epoch (index of this validator set)
  -> Chain
  -> [Attestation]  -- ^ payload sealed into the block
  -> [Vote]
  -> Either String (Chain, Block, QuorumCert)
finalise vs epoch chain payload votes =
  let endorsers  = filter voteSign votes
      samples    = map voteClock endorsers
      blockTime  = medianTime samples
      mroot      = merkleRoot (map attestationLeaf payload)
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
