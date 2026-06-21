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

import           Data.List      (elemIndex, nub)
import           Sanctum.Crypto
import           Sanctum.Core   (quorumThreshold)
import           Sanctum.Types

----------------------------------------------------------------------
-- Hashing
----------------------------------------------------------------------

headerHash :: BlockHeader -> Hash
headerHash h = tagged DHeader
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
attestationLeaf a =
  attestationDigest (attAuthor a) (factDigest (attFact a)) (attClaimedTime a)

-- | The number of DISTINCT validator-set members whose signature over
--   @msg@ verifies.  Quorum decisions count THIS, never a self-declared
--   boolean vector — so a certificate cannot claim signatures it lacks.
countValidSigners :: ValidatorSet -> Hash -> [(Identity, Sig)] -> Int
countValidSigners vs msg sigs =
  length (nub [ idn | (idn, s) <- sigs
                    , idn `elem` vsetMembers vs
                    , verify idn msg s ])

----------------------------------------------------------------------
-- Merkle tree
--
-- The published root binds the LEAF COUNT (`merkleRoot`/`merkleVerify`
-- fold over a bare tree, then domain-separate with the count).  This
-- defeats the duplicate-last second-preimage (CVE-2012-2459): a tree of
-- n leaves and one of n+1 with a duplicated tail no longer share a root,
-- because their counts differ.
----------------------------------------------------------------------

hpair :: Hash -> Hash -> Hash
hpair a b = tagged DNode [unHash a, unHash b]

-- root of the bare tree (duplicate-last for odd levels)
bareRoot :: [Hash] -> Hash
bareRoot []  = zeroHash
bareRoot [x] = x
bareRoot xs  = bareRoot (pairUp xs)
  where
    pairUp (a : b : rest) = hpair a b : pairUp rest
    pairUp [a]            = [hpair a a]
    pairUp []             = []

-- | The count-bound Merkle root committed to in the header.
merkleRoot :: [Hash] -> Hash
merkleRoot xs = tagged DRoot [fromIntegral (length xs), unHash (bareRoot xs)]

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

-- | Recompute the count-bound root from a leaf, its index, the sibling
--   path, and the total leaf count, then compare to the published root.
--   Rejects structurally inconsistent witnesses up front (index in range,
--   path depth matching the count) before trusting the root reproduction.
merkleVerify :: Hash -> Int -> [Hash] -> Int -> Hash -> Bool
merkleVerify leaf i path count root =
     i >= 0 && i < count
  && length path == treeDepth count
  && tagged DRoot [fromIntegral count, unHash (fold leaf i path)] == root
  where
    fold h _ []           = h
    fold h j (sib : sibs) =
      fold (if even j then hpair h sib else hpair sib h) (j `div` 2) sibs

-- depth of the duplicate-last binary tree over n leaves (0 for n ≤ 1)
treeDepth :: Int -> Int
treeDepth n = go n 0
  where go k d = if k <= 1 then d else go ((k + 1) `div` 2) (d + 1)

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
      , tLeafCount   = length (blkAttestations blk)
      }

-- | Verify a Testament using ONLY the testament itself (no network).
--   Requires the *expected* validator set (anchored to genesis lineage);
--   in the air-gapped setting the recipient is provisioned with it once
--   (see docs/threat-model.md for the onboarding ceremony this assumes).
--
--   Checks, in order:
--     1. the author actually signed the attestation (author authenticity);
--     2. the attestation's leaf is included under the header's Merkle root;
--     3. ≥ n−f DISTINCT members signed the block header, counted from
--        *verified* signatures (not the certificate's boolean vector).
--   On success, returns the proven timestamp.
verifyTestament :: ValidatorSet -> Testament -> Either String Integer
verifyTestament expected t
  | tValidators t /= expected =
      Left "validator set does not match the trusted (genesis-anchored) set"
  | not (wellFormedVSet vs) =
      Left "trusted validator set is malformed (distinct members & n >= 3f+1 required)"
  | not authorSigned =
      Left "author signature on the attestation is invalid"
  | not inclusion =
      Left "Merkle inclusion failed: document not in the block"
  | validSigners < quorumThreshold n f =
      Left ("quorum not reached: only " ++ show validSigners
            ++ " verified signatures, need " ++ show (quorumThreshold n f))
  | otherwise = Right (hdrBlockTime (tHeader t))
  where
    vs           = tValidators t
    n            = validatorCount vs
    f            = faultBudget vs
    att          = tAttestation t
    leaf         = attestationLeaf att
    authorSigned = verify (attAuthor att) leaf (attSig att)
    inclusion    = merkleVerify leaf (tLeafIndex t)
                                (tMerklePath t) (tLeafCount t) (hdrMerkleRoot (tHeader t))
    -- the quorum is counted from signatures that actually verify over the
    -- header — the certificate's qcSigners vector is NOT trusted here.
    validSigners = countValidSigners vs (headerHash (tHeader t)) (qcSignatures (tCert t))

-- | The time a Testament proves the document existed by.
provenTime :: Testament -> Integer
provenTime = hdrBlockTime . tHeader

----------------------------------------------------------------------
-- Reconfiguration (Principle 5: the network grows)
----------------------------------------------------------------------

-- | Adopt a new validator set.  A reconfiguration is accepted only when a
--   quorum of the CURRENT set has *signed* a certificate that commits to
--   exactly the proposed members and the target epoch — so a stale or
--   forged certificate cannot install attacker validators (the central
--   reconfiguration attack).  Continuity is enforced so authority cannot
--   be handed off wholesale in one hop:
--
--     * the target epoch must be the immediate successor;
--     * the new set must satisfy n ≥ 3f+1;
--     * a quorum of the current set must persist into the new set
--       (no evicting more than f trusted members at once);
--     * the fault budget may rise by at most one per reconfiguration.
--
--   This is the concrete @Approves@ relation behind the abstract lineage
--   theorem in 'Sanctum.Proofs.Append'.
--
--   IMPORTANT (see docs/threat-model.md): these checks bound how *fast*
--   membership can change and guarantee each step is quorum-authorised and
--   anchored to genesis — but they do NOT guarantee the *honest fraction*
--   is preserved.  A coalition that already holds a current quorum can
--   migrate authority over several epochs; preventing that is an
--   out-of-protocol governance responsibility, not a property proved here.
adoptValidatorSet
  :: Int               -- ^ current epoch
  -> ValidatorSet      -- ^ current set
  -> [(Identity, Sig)] -- ^ current members' signatures over the reconfig digest
  -> Int               -- ^ target epoch (must be current + 1)
  -> ValidatorSet      -- ^ proposed new set
  -> Either String ValidatorSet
adoptValidatorSet currentEpoch current sigs toEpoch proposed
  | toEpoch /= currentEpoch + 1 =
      Left "reconfiguration rejected: target epoch must be current + 1"
  | not (wellFormedVSet current) =
      Left "reconfiguration rejected: current set is malformed"
  | not (wellFormedVSet proposed) =
      Left "reconfiguration rejected: new set malformed (distinct members & n >= 3f+1)"
  | faultBudget proposed > faultBudget current + 1 =
      Left "reconfiguration rejected: fault budget raised too fast"
  | validatorCount proposed > validatorCount current + 1 =
      Left "reconfiguration rejected: validator set may grow by at most one (net) per epoch"
  | overlap < currentQuorum =
      Left "reconfiguration rejected: a quorum of the current set must remain"
  | validSigners < currentQuorum =
      Left ("reconfiguration rejected: only " ++ show validSigners
            ++ " verified current-member signatures, need " ++ show currentQuorum)
  | otherwise = Right proposed
  where
    currentQuorum = quorumThreshold (validatorCount current) (faultBudget current)
    -- the signature binds the SOURCE (current members + epoch) and the
    -- TARGET (proposed members + epoch + fault), so it cannot be replayed.
    msg           = reconfigDigest (vsetMembers current) currentEpoch
                                   (vsetMembers proposed) toEpoch (faultBudget proposed)
    validSigners  = countValidSigners current msg sigs
    -- distinct overlap only (both sets are well-formed ⇒ already distinct)
    overlap       = length (filter (`elem` vsetMembers current) (vsetMembers proposed))
