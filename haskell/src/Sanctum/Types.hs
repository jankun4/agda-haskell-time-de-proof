-- | The domain types, following the seven principles (P0–P6).
module Sanctum.Types
  ( -- P1 Truth
    Fact(..)
    -- P3 Connection
  , Attestation(..)
  , attestationDigest
    -- P4 Structure
  , BlockHeader(..)
  , Block(..)
  , Chain
  , Height
    -- P5 Life
  , ValidatorSet(..)
  , QuorumCert(..)
  , validatorCount
  , faultBudget
  , wellFormedVSet
    -- P6 Harmony
  , Testament(..)
  , tDocument
  ) where

import           Data.Word     (Word64)
import           Sanctum.Crypto (Hash, Identity, Sig, hashConcat, digestText, unHash, unIdentity)

-- P1 · Truth/Being: a Fact is the existence of a document (its digest).
newtype Fact = Fact { factDigest :: Hash } deriving (Eq, Ord, Show)

-- P3 · Connection: an attestation binds author ↔ fact ↔ time by a sig.
data Attestation = Attestation
  { attAuthor      :: Identity
  , attFact        :: Fact
  , attClaimedTime :: Integer
  , attSig         :: Sig
  } deriving (Eq, Show)

-- The digest an attestation's signature covers: author ‖ fact ‖ time.
attestationDigest :: Identity -> Fact -> Integer -> Hash
attestationDigest author (Fact fh) t =
  hashConcat [ fromIntegral (unIdentity author), unHash fh, fromIntegral t ]

-- P4 · Structure: a block header and block.
data BlockHeader = BlockHeader
  { hdrParent     :: Hash
  , hdrMerkleRoot :: Hash
  , hdrBlockTime  :: Integer   -- BFT-agreed median time
  , hdrEpoch      :: Int       -- which validator set finalised it
  } deriving (Eq, Show)

data Block = Block
  { blkHeader       :: BlockHeader
  , blkAttestations :: [Attestation]
  } deriving (Eq, Show)

type Height = Int

-- The ledger is an append-only list of blocks (head = most recent).
type Chain = [Block]

-- P5 · Life: a validator set, tolerating @vsetFault@ Byzantine faults.
data ValidatorSet = ValidatorSet
  { vsetMembers :: [Identity]
  , vsetFault   :: Int
  } deriving (Eq, Show)

validatorCount :: ValidatorSet -> Int
validatorCount = length . vsetMembers

faultBudget :: ValidatorSet -> Int
faultBudget = vsetFault

-- Well-formed when n >= 3f+1 (the BFT bound the proofs assume).
wellFormedVSet :: ValidatorSet -> Bool
wellFormedVSet vs = validatorCount vs >= 3 * vsetFault vs + 1

-- A quorum certificate: which members signed and the clock each gave.
-- 'qcSigners' is the characteristic vector over 'vsetMembers' order;
-- 'qcSignatures' carries the actual signatures keyed by member index.
data QuorumCert = QuorumCert
  { qcSigners    :: [Bool]
  , qcSamples    :: [Integer]
  , qcSignatures :: [(Identity, Sig)]
  } deriving (Eq, Show)

-- P6 · Harmony: the offline-verifiable proof of existence-by-time.
-- It carries the full attestation so the verifier can recompute the
-- exact Merkle leaf (author ‖ fact ‖ time) that was committed.
data Testament = Testament
  { tAttestation :: Attestation
  , tHeader      :: BlockHeader
  , tValidators  :: ValidatorSet
  , tCert        :: QuorumCert
  , tMerklePath  :: [Hash]      -- inclusion path of the attestation leaf
  , tLeafIndex   :: Int
  } deriving (Eq, Show)

tDocument :: Testament -> Fact
tDocument = attFact . tAttestation
