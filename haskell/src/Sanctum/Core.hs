-- | The verified core, in Haskell.
--
-- Every function here is a transcription of @Sanctum.Kernel@ (Agda) and
-- can be replaced verbatim by the MAlonzo-extracted code that
-- @../scripts/extract.sh@ generates.  The theorems that make these
-- functions safe live in @../agda/src/Sanctum/Proofs/@:
--
--   * 'quorumReached'  ↔  Sanctum.Proofs.Quorum   (Agreement)
--   * 'medianTime'     ↔  Sanctum.Proofs.Time      (timestamp soundness*)
--   * 'runContract'    ↔  Sanctum.Kernel.runContract, which Agda accepts as
--                         a total (structurally-recursive) function — THAT
--                         is the totality witness for the language the node
--                         runs.  Sanctum.Proofs.Totality independently proves
--                         a richer STLC-with-rec evaluator total, showing the
--                         technique scales; it is not the executed language.
--
-- Because the executed evaluator is total (Agda accepts 'Kernel.runContract'),
-- the node needs neither gas nor fees: every contract provably halts.
-- (*) Time soundness is proved for a value with the median property; that
-- 'medianTime' yields such a value is tested, not yet proved — see
-- docs/limitations.md.
module Sanctum.Core
  ( -- * Quorum rule
    countTrue
  , quorumThreshold
  , quorumReached
    -- * BFT median time
  , insertSorted
  , sortNats
  , medianTime
    -- * Total on-chain contracts
  , Expr(..)
  , runContract
  ) where

----------------------------------------------------------------------
-- Quorum rule  (mirror of Sanctum.Kernel.quorumReached)
----------------------------------------------------------------------

countTrue :: [Bool] -> Int
countTrue = length . filter id

-- | A quorum needs "all but f" of the n validators: n − f signatures.
--   At n = 3f+1 this is the classic 2f+1; for n > 3f+1 it scales so that
--   any two quorums still intersect in an honest validator (the proof
--   obligation 2q ≥ n+f+1 holds for q = n−f exactly when n ≥ 3f+1).
-- Saturating subtraction, matching the Agda kernel's ℕ monus (n ∸ f) so
-- the Haskell mirror cannot diverge from the proof on malformed inputs.
quorumThreshold :: Int -> Int -> Int
quorumThreshold n f = max 0 (n - f)

quorumReached :: Int -> Int -> [Bool] -> Bool
quorumReached n f signers = countTrue signers >= quorumThreshold n f

----------------------------------------------------------------------
-- BFT median time  (mirror of Sanctum.Kernel.medianTime)
--
-- The block time is the median of the validators' clock samples.  With
-- at most f Byzantine clocks among 2f+1, the median is bounded by the
-- honest clocks (proved: Sanctum.Proofs.Time.median-bound).
----------------------------------------------------------------------

insertSorted :: Integer -> [Integer] -> [Integer]
insertSorted x []       = [x]
insertSorted x (y : ys) = if x <= y then x : y : ys else y : insertSorted x ys

sortNats :: [Integer] -> [Integer]
sortNats = foldr insertSorted []

medianTime :: [Integer] -> Integer
medianTime [] = 0
medianTime xs = sortNats xs !! (length xs `div` 2)

----------------------------------------------------------------------
-- Total on-chain contract language  (mirror of Sanctum.Kernel.Expr)
----------------------------------------------------------------------

data Expr
  = Lit Integer
  | Add Expr Expr
  | Mul Expr Expr
  | Ite Expr Expr Expr      -- ^ if c /= 0 then a else b
  | Leq Expr Expr           -- ^ 1 if a <= b else 0
  deriving (Eq, Show)

-- | Total evaluator — structurally recursive, always halts.
runContract :: Expr -> Integer
runContract (Lit n)     = n
runContract (Add a b)   = runContract a + runContract b
runContract (Mul a b)   = runContract a * runContract b
runContract (Ite c a b) = if runContract c /= 0 then runContract a else runContract b
runContract (Leq a b)   = if runContract a <= runContract b then 1 else 0
