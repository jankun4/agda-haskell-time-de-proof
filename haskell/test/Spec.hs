{-# LANGUAGE OverloadedStrings #-}

-- | Property/unit checks for the node, mirroring the Agda theses and
-- locking in the fixes from the council review (forgeable-quorum,
-- author-signature, quorum threshold n−f, signed reconfiguration).
module Main (main) where

import           Control.Monad (unless)
import           System.Exit   (exitFailure)
import           System.IO     (hSetEncoding, stdout, utf8)
import           Data.IORef
import           Sanctum.Crypto
import           Sanctum.Core
import           Sanctum.Types
import           Sanctum.Ledger
import           Sanctum.Consensus
import           Sanctum.Node

check :: IORef Int -> String -> Bool -> IO ()
check ref name ok = do
  putStrLn ((if ok then "[pass] " else "[FAIL] ") ++ name)
  unless ok (modifyIORef' ref (+1))

-- A tiny deterministic LCG, so property tests need no external dep.
lcg :: Int -> Int
lcg x = (1103515245 * x + 12345) `mod` 2147483648

stream :: Int -> [Int]
stream = tail . iterate lcg

main :: IO ()
main = do
  hSetEncoding stdout utf8
  fails <- newIORef (0 :: Int)
  let c = check fails

  -- ── Core: quorum rule (threshold n−f) ──────────────────────────────
  c "quorum n-f reached at 3 of 4 (n=4,f=1)" (quorumReached 4 1 [True,True,True,False])
  c "quorum not reached at 2 of 4 (n=4,f=1)" (not (quorumReached 4 1 [True,True,False,False]))
  c "quorum scales: n=7,f=2 needs 5"
    (quorumReached 7 2 (replicate 5 True ++ replicate 2 False)
     && not (quorumReached 7 2 (replicate 4 True ++ replicate 3 False)))

  -- ── Core: median rejects a Byzantine outlier (Time thesis) ─────────
  c "median ignores one Byzantine clock" (medianTime [1000,1001,1002,999999] == 1002)
  c "median of honest cluster stays in range"
    (let m = medianTime [50,51,52] in m >= 50 && m <= 52)

  -- ── Core: contracts are total and deterministic (Totality thesis) ──
  c "contract evaluates (no gas)" (runContract (Mul (Lit 7) (Lit 6)) == 42)
  c "contract if-branch" (runContract (Ite (Leq (Lit 5) (Lit 3)) (Lit 1) (Lit 0)) == 0)

  -- ── Signatures distinguish authors ────────────────────────────────
  let h   = mkHospital "A" 1
      h2  = mkHospital "B" 2
      d   = digestText "doc"
      sg  = sign (hSecret h) d
  c "valid signature verifies" (verify (hId h) d sg)
  c "signature rejected under wrong key" (not (verify (hId h2) d sg))

  -- ── End-to-end: finalise, build & verify a Testament; tamper fails ─
  let hC = mkHospital "C" 3
      hD = mkHospital "D" 4
      vs = ValidatorSet [hId h, hId h2, hId hC, hId hD] 1
      att = makeAttestation h "consent" 1000
      votes = [ Vote (hId h)  (hSecret h)  1000 True
              , Vote (hId h2) (hSecret h2) 1001 True
              , Vote (hId hC) (hSecret hC) 1002 True
              , Vote (hId hD) (hSecret hD) 777  True ]
  case finalise vs 0 [] [att] votes of
    Left e -> c ("finalise round: " ++ e) False
    Right (chain, blk, cert) -> do
      c "block appended" (length chain == 1)
      c "append-only: head links to genesis" (hdrParent (blkHeader blk) == zeroHash)
      case buildTestament vs blk cert att of
        Left e  -> c ("buildTestament: " ++ e) False
        Right t -> do
          c "Testament verifies offline"
            (verifyTestament vs t == Right (hdrBlockTime (blkHeader blk)))
          -- tamper the document → recomputed leaf changes → rejected
          let t1 = t { tAttestation = (tAttestation t) { attFact = Fact (digestText "ALTERED") } }
          c "tampered Testament rejected"
            (either (const True) (const False) (verifyTestament vs t1))
          -- REGRESSION (council C1): a cert that DECLARES a full quorum in
          -- its boolean vector but carries no real signatures must NOT pass.
          let t2 = t { tCert = (tCert t) { qcSigners = replicate 4 True, qcSignatures = [] } }
          c "forged quorum (signers vector, no signatures) rejected"
            (either (const True) (const False) (verifyTestament vs t2))
          -- REGRESSION: stripping the author's signature must be caught.
          let t3 = t { tAttestation = (tAttestation t) { attSig = sign (hSecret h2) (digestText "x") } }
          c "missing/forged author signature rejected"
            (either (const True) (const False) (verifyTestament vs t3))

  -- ── Reconfiguration safety (council C1/H5): signed + continuous ────
  let hE      = mkHospital "E" 5
      newSet  = ValidatorSet (vsetMembers vs ++ [hId hE]) 1   -- n=5, f=1
      msg     = reconfigDigest (vsetMembers newSet) 1 (vsetFault newSet)
      goodSigs = [ (hId h,  sign (hSecret h)  msg)
                 , (hId h2, sign (hSecret h2) msg)
                 , (hId hC, sign (hSecret hC) msg) ]            -- quorum (3 of 4)
      tooFew   = take 2 goodSigs
  c "reconfig adopted with signed quorum"
    (either (const False) (const True) (adoptValidatorSet 0 vs goodSigs 1 newSet))
  c "reconfig rejected: too few signatures"
    (either (const True) (const False) (adoptValidatorSet 0 vs tooFew 1 newSet))
  c "reconfig rejected: empty (unsigned) certificate"
    (either (const True) (const False) (adoptValidatorSet 0 vs [] 1 newSet))
  c "reconfig rejected: wrong target epoch"
    (either (const True) (const False) (adoptValidatorSet 0 vs goodSigs 5 newSet))
  -- replay: signatures over a DIFFERENT set must not authorise this one
  let otherMsgSigs = [ (hId h,  sign (hSecret h)  (reconfigDigest (vsetMembers vs) 1 1)) ]
  c "reconfig rejected: signatures bound to a different set"
    (either (const True) (const False) (adoptValidatorSet 0 vs otherMsgSigs 1 newSet))

  -- ── Property tests (randomised, base-only) ─────────────────────────
  -- medianTime always lands within [min,max] of its inputs.
  let medianBatches = take 200 (chunk 5 (map ((`mod` 1000) . abs) (stream 7)))
  c "property: median ∈ [min,max] over 200 random samples"
    (all (\xs -> not (null xs) `implies`
                 (let m = medianTime (map toInteger xs)
                  in m >= toInteger (minimum xs) && m <= toInteger (maximum xs)))
         medianBatches)
  -- quorumReached is monotone in the signature count.
  c "property: quorumReached monotone in #signatures"
    (all (\k -> quorumReached 7 2 (replicate k True ++ replicate (7-k) False)
                  `implies2` quorumReached 7 2 (replicate (k+1) True ++ replicate (6-k) False))
         [0..4])

  n <- readIORef fails
  if n == 0 then putStrLn "\nAll tests passed."
            else putStrLn ("\n" ++ show n ++ " test(s) failed.") >> exitFailure

implies :: Bool -> Bool -> Bool
implies a b = not a || b

implies2 :: Bool -> Bool -> Bool
implies2 = implies

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk k xs = let (a,b) = splitAt k xs in a : chunk k b
