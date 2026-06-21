-- | The domain types, following the seven principles (P0–P6).
module Sanctum.Types
  ( -- P1 Truth
    Fact(..)
    -- P3 Connection
  , Attestation(..)
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

import           Data.List      (nub)
import           Sanctum.Crypto (Hash, Identity, Sig)

-- P1 · Truth/Being: a Fact is the existence of a document (its digest).
newtype Fact = Fact { factDigest :: Hash } deriving (Eq, Ord, Show)

-- P3 · Connection: an attestation binds author ↔ fact ↔ time by a sig.
-- (The digest its signature covers is 'Sanctum.Crypto.attestationDigest'.)
data Attestation = Attestation
  { attAuthor      :: Identity
  , attFact        :: Fact
  , attClaimedTime :: Integer
  , attSig         :: Sig
  } deriving (Eq, Show)

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

-- Well-formed when members are DISTINCT and n >= 3f+1 (the BFT bound the
-- proofs assume).  Distinctness matters: duplicate identities would let a
-- single party occupy several quorum slots and inflate overlap/size,
-- breaking the honest-majority premise the Agda proof relies on.
wellFormedVSet :: ValidatorSet -> Bool
wellFormedVSet vs =
  vsetMembers vs == nub (vsetMembers vs)
  && validatorCount vs >= 3 * vsetFault vs + 1

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
  , tLeafCount   :: Int         -- total leaves (binds the tree size; anti-CVE-2012-2459)
  } deriving (Eq, Show)

tDocument :: Testament -> Fact
tDocument = attFact . tAttestation
