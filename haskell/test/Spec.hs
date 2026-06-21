{-# LANGUAGE OverloadedStrings #-}

-- | Property/unit checks for the node, mirroring the Agda theses.
module Main (main) where

import           Control.Monad (unless, forM_)
import           System.Exit   (exitFailure)
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

main :: IO ()
main = do
  fails <- newIORef (0 :: Int)
  let c = check fails

  -- Core: quorum rule (Quorum thesis)
  c "quorum 2f+1 reached at exactly 3 of 4 (f=1)" (quorumReached 1 [True,True,True,False])
  c "quorum not reached at 2 of 4 (f=1)" (not (quorumReached 1 [True,True,False,False]))

  -- Core: median rejects a Byzantine outlier (Time thesis)
  c "median ignores one Byzantine clock" (medianTime [1000,1001,1002,999999] == 1002)
  c "median of honest cluster stays in range"
    (let m = medianTime [50,51,52] in m >= 50 && m <= 52)

  -- Core: contracts are total and deterministic (Totality thesis)
  c "contract evaluates (no gas)" (runContract (Mul (Lit 7) (Lit 6)) == 42)
  c "contract if-branch" (runContract (Ite (Leq (Lit 5) (Lit 3)) (Lit 1) (Lit 0)) == 0)

  -- Signatures distinguish authors
  let h   = mkHospital "A" 1
      h2  = mkHospital "B" 2
      d   = digestText "doc"
      sg  = sign (hSecret h) d
  c "valid signature verifies" (verify (hId h) d sg)
  c "signature rejected under wrong key" (not (verify (hId h2) d sg))

  -- End-to-end: finalise, build & verify a Testament; tamper fails
  let vs = ValidatorSet [hId h, hId h2, hId (mkHospital "C" 3), hId (mkHospital "D" 4)] 1
      hC = mkHospital "C" 3
      hD = mkHospital "D" 4
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
          c "Testament verifies offline" (verifyTestament vs t == Right (hdrBlockTime (blkHeader blk)))
          let t' = t { tAttestation = (tAttestation t) { attFact = Fact (digestText "ALTERED") } }
          c "tampered Testament rejected" (either (const True) (const False) (verifyTestament vs t'))

  -- Reconfiguration safety
  let newSet = ValidatorSet (vsetMembers vs ++ [hId (mkHospital "E" 5)]) 1
      okCert = QuorumCert [True,True,True,True] [] []
      noCert = QuorumCert [True,False,False,False] [] []
  c "reconfig adopted with quorum" (either (const False) (const True) (adoptValidatorSet vs okCert newSet))
  c "reconfig rejected without quorum" (either (const True) (const False) (adoptValidatorSet vs noCert newSet))

  n <- readIORef fails
  if n == 0 then putStrLn "\nAll tests passed."
            else putStrLn ("\n" ++ show n ++ " test(s) failed.") >> exitFailure
