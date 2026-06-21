-- | Principle 5/6: the genesis-anchored AUTHORITY LINEAGE for offline
--   verifiers.
--
-- The deepest hole the review council kept flagging: an air-gapped site
-- verified a Testament against a *bare* validator set it was simply handed,
-- with no way to confirm that set descends from a trusted genesis — and,
-- once the network reconfigures, a genesis-provisioned verifier could not
-- validate later-epoch Testaments at all.
--
-- This module closes both: a verifier is provisioned ONCE with a signed
-- founding 'Charter' (the genesis set, signed by all founders). To check a
-- Testament from epoch e, it walks a chain of reconfiguration steps from the
-- charter, RE-VERIFYING each step with the very same 'adoptValidatorSet'
-- rule the online nodes use (quorum-signed, source+target-bound, continuous).
-- The validator set it ends up trusting is therefore provably descended from
-- genesis — offline, with no network. This is the concrete, runnable
-- counterpart of the abstract @authorised→lineage@ theorem in
-- @Sanctum.Proofs.Append@.
module Sanctum.Lineage
  ( Charter(..)
  , charterDigest
  , verifyCharter
  , ReconfigStep(..)
  , verifyLineageTo
  , verifyTestamentFromCharter
  ) where

import           Data.List       (nub)
import           Sanctum.Crypto
import           Sanctum.Types
import           Sanctum.Ledger  (adoptValidatorSet, verifyTestament)

----------------------------------------------------------------------
-- The founding charter
----------------------------------------------------------------------

-- | The single root of trust: the genesis validator set, signed by every
--   founding hospital.  An air-gapped verifier is provisioned with this
--   (and ideally checks the founders' key fingerprints out-of-band — see
--   docs/threat-model.md for the onboarding ceremony).
data Charter = Charter
  { charterGenesis  :: ValidatorSet
  , charterSigs     :: [(Identity, Sig)]   -- each genesis member's signature
  } deriving (Eq, Show)

-- | The digest a charter commits to: the genesis members and fault budget.
charterDigest :: ValidatorSet -> Hash
charterDigest vs =
  tagged DCharter ( fromIntegral (faultBudget vs)
                  : fromIntegral (validatorCount vs)
                  : map (fromIntegral . unIdentity) (vsetMembers vs) )

-- | Verify a charter: the genesis set is well-formed and EVERY genesis
--   member has signed it.  Returns the trusted genesis set (epoch 0).
verifyCharter :: Charter -> Either String ValidatorSet
verifyCharter (Charter genesis sigs)
  | not (wellFormedVSet genesis) =
      Left "charter rejected: genesis set malformed"
  | signedMembers /= length (vsetMembers genesis) =
      Left "charter rejected: not every founding member signed the genesis set"
  | otherwise = Right genesis
  where
    msg           = charterDigest genesis
    signedMembers =
      length (nub [ idn | idn <- vsetMembers genesis
                        , (s, sg) <- sigs, s == idn, verify idn msg sg ])

----------------------------------------------------------------------
-- The reconfiguration lineage
----------------------------------------------------------------------

-- | One adopted reconfiguration: the new set and the current set's
--   signatures over the reconfig digest (exactly what 'adoptValidatorSet'
--   consumes).
data ReconfigStep = ReconfigStep
  { rsToSet :: ValidatorSet
  , rsSigs  :: [(Identity, Sig)]
  } deriving (Eq, Show)

-- | Walk the lineage from the charter genesis (epoch 0), re-verifying
--   EVERY step with 'adoptValidatorSet', and return the validator set in
--   force at @targetEpoch@.  The whole provided lineage is verified (no
--   trailing step is trusted unchecked), and the two failure modes are
--   kept distinct: a *malformed/forged step* ("invalid") versus simply
--   *not enough steps* to reach the epoch ("incomplete") — so an operator
--   can tell forgery from a withheld/short lineage (Agent 5 H, Agent 0).
verifyLineageTo :: Charter -> [ReconfigStep] -> Int -> Either String ValidatorSet
verifyLineageTo charter steps targetEpoch
  | targetEpoch < 0 = Left "lineage: negative target epoch"
  | otherwise = do
      genesis <- verifyCharter charter
      sets    <- go 0 genesis steps     -- sets !! e = verified set in force at epoch e
      case drop targetEpoch sets of
        (s : _) -> Right s
        []      -> Left "lineage incomplete: not enough reconfiguration steps \
                        \to reach the Testament's epoch"
  where
    go _ current [] = Right [current]
    go epoch current (ReconfigStep next sigs : rest) =
      case adoptValidatorSet epoch current sigs (epoch + 1) next of
        Left e        -> Left ("lineage invalid at epoch " ++ show epoch
                               ++ "->" ++ show (epoch + 1) ++ ": " ++ e)
        Right adopted -> (current :) <$> go (epoch + 1) adopted rest

----------------------------------------------------------------------
-- Offline Testament verification anchored to genesis
----------------------------------------------------------------------

-- | Verify a Testament using ONLY a charter and the reconfiguration
--   lineage — no trusted-set argument, no network.  The verifier walks
--   from genesis to the Testament's epoch, then checks the Testament
--   against the set it derived (which must match the header's epoch).
verifyTestamentFromCharter
  :: Charter -> [ReconfigStep] -> Testament -> Either String Integer
verifyTestamentFromCharter charter steps t = do
  vs <- verifyLineageTo charter steps (hdrEpoch (tHeader t))
  verifyTestament vs t
