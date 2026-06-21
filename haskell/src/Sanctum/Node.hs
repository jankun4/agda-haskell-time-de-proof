-- | Node-level conveniences: hospital identities and attestations.
--
-- A "hospital" is a node holding a keypair.  Some hospitals are also
-- validators (they vote in consensus); some are air-gapped and only ever
-- *verify* Testaments offline.  This module provides the small glue the
-- demo and tests use; it is intentionally thin — all the load-bearing
-- logic lives in 'Sanctum.Ledger' / 'Sanctum.Consensus' / 'Sanctum.Core'.
module Sanctum.Node
  ( Hospital(..)
  , mkHospital
  , makeAttestation
  ) where

import           Data.Text     (Text)
import           Data.Word     (Word64)
import           Sanctum.Crypto
import           Sanctum.Types

-- | A hospital node: a human-readable name and a keypair.
data Hospital = Hospital
  { hName   :: String
  , hId     :: Identity
  , hSecret :: SecretKey
  } deriving (Show)

-- | Deterministically derive a hospital from a seed (demo).
mkHospital :: String -> Word64 -> Hospital
mkHospital name seed =
  let (idn, sk) = keypair seed
  in Hospital name idn sk

-- | A hospital signs a document at a claimed time, producing an
--   attestation that the document existed.
makeAttestation :: Hospital -> Text -> Integer -> Attestation
makeAttestation h docText claimedT =
  let fact   = Fact (digestText docText)
      digest = attestationDigest (hId h) (factDigest fact) claimedT
      s      = sign (hSecret h) digest
  in Attestation
       { attAuthor      = hId h
       , attFact        = fact
       , attClaimedTime = claimedT
       , attSig         = s
       }
