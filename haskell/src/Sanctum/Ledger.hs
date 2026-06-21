-- | Principle 4 (Structure) + Principle 6 (Harmony): the append-only
--   ledger, Merkle commitments, and the offline-verifiable Testament.
module Sanctum.Ledger
  ( -- * Hashing blocks
    headerHash
  , headHash
  , attestationLeaf
    -- * Merkle commitments
  , merkleRoot
  , merklePath
  , merkleVerify
    -- * Chain validation (append-only)
  , validNext
  , appendBlock
    -- * Testament (offline proof of existence-by-time)
  , buildTestament
  , verifyTestament
  , provenTime
    -- * Reconfiguration (Principle 5: growth)
  , adoptValidatorSet
  ) where

import           Data.List      (elemIndex)
import           Sanctum.Crypto
import           Sanctum.Core   (quorumReached, countTrue)
import           Sanctum.Types

----------------------------------------------------------------------
-- Hashing
----------------------------------------------------------------------

headerHash :: BlockHeader -> Hash
headerHash h = hashConcat
  [ unHash (hdrParent h)
  , unHash (hdrMerkleRoot h)
  , fromIntegral (hdrBlockTime h)
  , fromIntegral (hdrEpoch h)
  ]

-- | Hash of the chain head (zeroHash for the empty/genesis-less chain).
headHash :: Chain -> Hash
headHash []      = zeroHash
headHash (b : _) = headerHash (blkHeader b)

-- | A Merkle leaf for an attestation = the digest its signature covers.
attestationLeaf :: Attestation -> Hash
attestationLeaf a = attestationDigest (attAuthor a) (attFact a) (attClaimedTime a)

----------------------------------------------------------------------
-- Merkle tree (duplicate-last for odd levels)
----------------------------------------------------------------------

hpair :: Hash -> Hash -> Hash
hpair a b = hashConcat [unHash a, unHash b]

merkleRoot :: [Hash] -> Hash
merkleRoot []  = zeroHash
merkleRoot [x] = x
merkleRoot xs  = merkleRoot (pairUp xs)
  where
    pairUp (a : b : rest) = hpair a b : pairUp rest
    pairUp [a]            = [hpair a a]
    pairUp []             = []

-- | The sibling path proving leaf @i@'s membership.
merklePath :: [Hash] -> Int -> [Hash]
merklePath xs i
  | length xs <= 1 = []
  | otherwise =
      let sib = if even i
                  then safeAt xs (i + 1) (safeAt xs i zeroHash)  -- right sibling (dup if absent)
                  else safeAt xs (i - 1) zeroHash
      in sib : merklePath (pairUp xs) (i `div` 2)
  where
    pairUp (a : b : rest) = hpair a b : pairUp rest
    pairUp [a]            = [hpair a a]
    pairUp []             = []

safeAt :: [a] -> Int -> a -> a
safeAt xs i d = if i >= 0 && i < length xs then xs !! i else d

-- | Recompute the root from a leaf, its index, and its sibling path.
merkleVerify :: Hash -> Int -> [Hash] -> Hash -> Bool
merkleVerify leaf _ [] root = leaf == root
merkleVerify leaf i (sib : sibs) root =
  let combined = if even i then hpair leaf sib else hpair sib leaf
  in merkleVerify combined (i `div` 2) sibs root

----------------------------------------------------------------------
-- Append-only chain validation
----------------------------------------------------------------------

-- | Is @blk@ a valid extension of @chain@?  Its parent must be the head,
--   and its Merkle root must commit exactly to its attestations.
validNext :: Chain -> Block -> Bool
validNext chain blk =
  hdrParent (blkHeader blk) == headHash chain
  && hdrMerkleRoot (blkHeader blk) == merkleRoot (map attestationLeaf (blkAttestations blk))

appendBlock :: Chain -> Block -> Either String Chain
appendBlock chain blk
  | validNext chain blk = Right (blk : chain)
  | otherwise           = Left "block does not extend the chain (parent/merkle mismatch)"

----------------------------------------------------------------------
-- Testament: a self-contained, OFFLINE-verifiable proof.
----------------------------------------------------------------------

-- | Build a Testament for an attestation sealed in a finalised block.
buildTestament :: ValidatorSet -> Block -> QuorumCert -> Attestation -> Either String Testament
buildTestament vs blk cert att =
  case elemIndex att (blkAttestations blk) of
    Nothing -> Left "attestation is not in that block"
    Just i  -> Right Testament
      { tAttestation = att
      , tHeader      = blkHeader blk
      , tValidators  = vs
      , tCert        = cert
      , tMerklePath  = merklePath (map attestationLeaf (blkAttestations blk)) i
      , tLeafIndex   = i
      }

-- | Verify a Testament using ONLY the testament itself (no network).
--   Requires the *expected* validator set (anchored to genesis lineage);
--   in the air-gapped setting the recipient is provisioned with it once.
--
--   Checks, in order:
--     1. the document's leaf is included under the header's Merkle root;
--     2. ≥ 2f+1 distinct members signed the block header (quorum);
--     3. every certificate signature verifies under a member's key.
--   On success, returns the proven timestamp.
verifyTestament :: ValidatorSet -> Testament -> Either String Integer
verifyTestament expected t
  | tValidators t /= expected =
      Left "validator set does not match the trusted (genesis-anchored) set"
  | not inclusion =
      Left "Merkle inclusion failed: document not in the block"
  | not (quorumReached f signersVec) =
      Left "quorum not reached: fewer than 2f+1 signatures"
  | not allSigsValid =
      Left "a certificate signature failed verification"
  | not signersAreMembers =
      Left "a signature came from a non-member"
  | otherwise = Right (hdrBlockTime (tHeader t))
  where
    vs          = tValidators t
    f           = faultBudget vs
    cert        = tCert t
    -- recompute the exact committed leaf from the carried attestation
    leaf        = attestationLeaf (tAttestation t)
    inclusion   = merkleVerify leaf (tLeafIndex t)
                               (tMerklePath t) (hdrMerkleRoot (tHeader t))
    signersVec  = qcSigners cert
    hHash       = headerHash (tHeader t)
    allSigsValid      = all (\(idn, s) -> verify idn hHash s) (qcSignatures cert)
    signersAreMembers = all (\(idn, _) -> idn `elem` vsetMembers vs) (qcSignatures cert)

-- | The time a Testament proves the document existed by.
provenTime :: Testament -> Integer
provenTime = hdrBlockTime . tHeader

----------------------------------------------------------------------
-- Reconfiguration (Principle 5: the network grows)
----------------------------------------------------------------------

-- | Adopt a new validator set, but only if a quorum of the CURRENT set
--   certifies it.  This is the on-ledger reconfiguration; the resulting
--   authority lineage back to genesis is what 'Sanctum.Proofs.Append'
--   (authorised→lineage) guarantees.
adoptValidatorSet
  :: ValidatorSet     -- ^ current set
  -> QuorumCert       -- ^ current set's certificate over the new set
  -> ValidatorSet     -- ^ proposed new set
  -> Either String ValidatorSet
adoptValidatorSet current cert proposed
  | not (quorumReached (faultBudget current) (qcSigners cert)) =
      Left "reconfiguration rejected: current set did not reach quorum"
  | not (wellFormedVSet proposed) =
      Left "reconfiguration rejected: new set violates n >= 3f+1"
  | otherwise = Right proposed
