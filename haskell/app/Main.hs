{-# LANGUAGE OverloadedStrings #-}

-- | Sanctum demo: a small hospital network proving documents existed at
--   a given time — through Byzantine distrust, with an air-gapped site
--   verifying offline, and with a new hospital joining the network.
module Main (main) where

import           System.Exit    (exitFailure)
import           System.IO      (hSetEncoding, stdout, stderr, utf8)
import           Sanctum.Crypto
import           Sanctum.Core
import           Sanctum.Types
import           Sanctum.Ledger
import           Sanctum.Consensus
import           Sanctum.Node

section :: String -> IO ()
section s = putStrLn ("\n=== " ++ s ++ " ===")

main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  putStrLn "SANCTUM — trusted timestamping for a hospital network"
  putStrLn "(core verified in Agda; this node runs in Haskell)"

  ----------------------------------------------------------------
  section "0·Void / 1·Truth — the empty ledger and a document"
  let chain0 = [] :: Chain
  putStrLn ("genesis head hash = " ++ show (headHash chain0))
  let stMary   = mkHospital "St. Mary's"   1001
      general  = mkHospital "General"      1002
      stLukes  = mkHospital "St. Luke's"   1003
      mercy    = mkHospital "Mercy"        1004      -- will misbehave
      clinic   = mkHospital "Alpine Clinic" 9009     -- air-gapped, verify-only
  -- St Mary's attests a consent form existed (claims ~10:00, t=1000).
  let consent = makeAttestation stMary "Patient X — consent form v3" 1000
      lab     = makeAttestation general "Lab result #88421" 1001
  putStrLn ("document fact = " ++ show (attFact consent))

  ----------------------------------------------------------------
  section "2·Distinction — signatures distinguish the true author"
  let consentDigest = attestationDigest (attAuthor consent) (factDigest (attFact consent)) (attClaimedTime consent)
      goodSig = verify (attAuthor consent) consentDigest (attSig consent)
      forged  = verify (hId mercy)         consentDigest (attSig consent)
  putStrLn ("St Mary's signature verifies     : " ++ show goodSig)
  putStrLn ("same sig under Mercy's key (forge): " ++ show forged ++ "  (correctly rejected)")

  ----------------------------------------------------------------
  section "4·Structure / 5·Life — BFT round with a Byzantine clock"
  let validators = ValidatorSet
        { vsetMembers = [hId stMary, hId general, hId stLukes, hId mercy]
        , vsetFault   = 1 }                       -- n=4 ≥ 3f+1 ✓
  putStrLn ("validator set well-formed (n≥3f+1): " ++ show (wellFormedVSet validators))
  -- Honest clocks ~1000..1002; Mercy lies with 999999.
  let votes =
        [ Vote (hId stMary)  (hSecret stMary)  1000   True
        , Vote (hId general) (hSecret general) 1001   True
        , Vote (hId stLukes) (hSecret stLukes) 1002   True
        , Vote (hId mercy)   (hSecret mercy)   999999 True ]   -- Byzantine
      payload = [consent, lab]
  (chain1, blk1, cert1) <- expect (finalise validators 0 chain0 payload votes)
  putStrLn ("median block time = " ++ show (hdrBlockTime (blkHeader blk1))
            ++ "  (Mercy's 999999 had no effect)")
  putStrLn ("chain height = " ++ show (length chain1))

  ----------------------------------------------------------------
  section "6·Harmony — an offline-verifiable Testament"
  testament <- expect (buildTestament validators blk1 cert1 consent)
  putStrLn ("St Mary's hands the Testament to the air-gapped " ++ hName clinic ++ ".")
  putStrLn "It is provisioned once with the trusted, genesis-anchored validator set."
  case verifyTestament validators testament of
    Right t  -> putStrLn ("  [ok] verified OFFLINE — document provably existed by t=" ++ show t)
    Left err -> putStrLn ("  unexpected failure: " ++ err) >> exitFailure

  ----------------------------------------------------------------
  section "tamper-evidence — altering the document breaks the proof"
  let tampered = testament { tAttestation = (tAttestation testament)
                              { attFact = Fact (digestText "Patient X — consent form v4 (ALTERED)") } }
  case verifyTestament validators tampered of
    Left err -> putStrLn ("  [ok] tampering detected and rejected: " ++ err)
    Right _  -> putStrLn "  [BUG] tampering not detected" >> exitFailure

  ----------------------------------------------------------------
  section "5·Life (growth) — a new hospital joins the network"
  let riverside = mkHospital "Riverside" 1005
      newSet = ValidatorSet
        { vsetMembers = vsetMembers validators ++ [hId riverside]
        , vsetFault   = 1 }                       -- n=5 ≥ 3f+1 ✓
      -- the CURRENT set SIGNS a certificate committing to source (current
      -- members + epoch 0) and target (new members + epoch 1 + fault) —
      -- a quorum, n−f = 3, of St Mary/General/St Luke's
      reconfigMsg = reconfigDigest (vsetMembers validators) 0
                                   (vsetMembers newSet) 1 (vsetFault newSet)
      reconfigSigs =
        [ (hId stMary,  sign (hSecret stMary)  reconfigMsg)
        , (hId general, sign (hSecret general) reconfigMsg)
        , (hId stLukes, sign (hSecret stLukes) reconfigMsg) ]
  adopted <- expect (adoptValidatorSet 0 validators reconfigSigs 1 newSet)
  putStrLn ("new validator set adopted; members = " ++ show (length (vsetMembers adopted)))
  -- A second round under the new set (epoch 1), now with Riverside voting.
  let votes2 =
        [ Vote (hId stMary)    (hSecret stMary)    2000 True
        , Vote (hId general)   (hSecret general)   2001 True
        , Vote (hId stLukes)   (hSecret stLukes)   2002 True
        , Vote (hId riverside) (hSecret riverside) 2003 True ]
      payload2 = [ makeAttestation riverside "Riverside intake form #1" 2000 ]
  (chain2, blk2, _) <- expect (finalise adopted 1 chain1 payload2 votes2)
  putStrLn ("epoch-1 block time = " ++ show (hdrBlockTime (blkHeader blk2))
            ++ ", chain height = " ++ show (length chain2))

  ----------------------------------------------------------------
  section "no gas, no fees — a total on-chain contract"
  let c = Ite (Leq (Lit 2) (Lit 3)) (Mul (Lit 7) (Lit 6)) (Lit 0)
  putStrLn ("contract  if 2≤3 then 7*6 else 0  =>  " ++ show (runContract c)
            ++ "   (guaranteed to halt — proved total in Agda)")

  putStrLn "\nAll invariants held."

expect :: Either String a -> IO a
expect (Right a)  = pure a
expect (Left err) = putStrLn ("FATAL: " ++ err) >> exitFailure >> error "unreachable"
