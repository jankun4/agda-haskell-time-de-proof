------------------------------------------------------------------------
-- THE KERNEL — the ultra-minimal, fully-total executable core.
--
-- This is the part of the node that is WRITTEN IN AGDA and EXTRACTED TO
-- HASKELL (`scripts/extract.sh`, GHC/MAlonzo backend).  Everything here
-- is total — accepted by Agda's termination checker — which is exactly
-- why the on-chain contract evaluator needs neither gas nor fees.
--
-- The kernel computes the three security-critical quantities the proofs
-- are about:
--
--   * `quorumReached` — does a certificate meet the n−f threshold?
--                        (safety: Sanctum.Proofs.Quorum, incl. deployment-bound)
--   * `medianTime`    — the BFT-agreed block time from clock samples.
--                        (soundness: Sanctum.Proofs.Time)
--   * `runContract`   — a total on-chain expression evaluator; Agda accepts
--                        it as structurally recursive, which IS its totality
--                        proof.  (Sanctum.Proofs.Totality proves a richer STLC
--                        total separately, as scalability headroom.)
--
-- `main` is a self-test demonstrating the extracted core running.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Sanctum.Kernel where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
  renaming (_<_ to _<ᵇ_; _==_ to _==ᵇ_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat using (_≤ᵇ_; _∸_)

------------------------------------------------------------------------
-- Counting signatories and the quorum rule.

countTrue : List Bool → Nat
countTrue []           = 0
countTrue (true  ∷ xs) = suc (countTrue xs)
countTrue (false ∷ xs) = countTrue xs

-- A quorum needs "all but f" of the n validators: n − f signatures.
-- (At n = 3f+1 this is the classic 2f+1; it scales for n > 3f+1 so that
--  quorum intersection still yields an honest validator — see
--  Sanctum.Proofs.Quorum.)
quorumThreshold : Nat → Nat → Nat
quorumThreshold n f = n ∸ f

quorumReached : Nat → Nat → List Bool → Bool
quorumReached n f signers = quorumThreshold n f ≤ᵇ countTrue signers

------------------------------------------------------------------------
-- The BFT-agreed block time: median of the validators' clock samples.
-- Insertion sort + middle element; total by structural recursion.

insert : Nat → List Nat → List Nat
insert x []       = x ∷ []
insert x (y ∷ ys) = if x ≤ᵇ y then x ∷ y ∷ ys else y ∷ insert x ys

sort : List Nat → List Nat
sort []       = []
sort (x ∷ xs) = insert x (sort xs)

-- the element at index n (saturating at the last element); total.
nth : Nat → List Nat → Nat
nth _       []           = 0
nth zero    (x ∷ _)      = x
nth (suc n) (x ∷ [])     = x
nth (suc n) (_ ∷ y ∷ ys) = nth n (y ∷ ys)

-- median: middle of the sorted samples.  ⌊len/2⌋.
half : Nat → Nat
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

medianTime : List Nat → Nat
medianTime xs = nth (half (length xs)) (sort xs)

------------------------------------------------------------------------
-- A total on-chain expression language (no gas needed — it always
-- halts).  First-order, so it extracts to clean Haskell.

data Expr : Set where
  lit  : Nat → Expr
  add  : Expr → Expr → Expr
  mul  : Expr → Expr → Expr
  ite  : Expr → Expr → Expr → Expr   -- if e≠0 then a else b
  leq  : Expr → Expr → Expr          -- 1 if a ≤ b else 0

runContract : Expr → Nat
runContract (lit n)     = n
runContract (add a b)   = runContract a + runContract b
runContract (mul a b)   = runContract a * runContract b
runContract (ite c a b) = if 0 <ᵇ runContract c
                          then runContract a else runContract b
runContract (leq a b)   = if runContract a ≤ᵇ runContract b
                          then 1 else 0

------------------------------------------------------------------------
-- Chain linkage check: a block's parentHash must equal the head hash.

linksTo : Nat → Nat → Bool          -- linksTo parentHash headHash
linksTo p head = p ==ᵇ head

------------------------------------------------------------------------
-- Self-test (runs after extraction to prove the core executes).

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Data.String using (String; _++_)
open import Data.Nat.Show using (show)
open import Data.Bool.Show using () renaming (show to showBool)

-- Minimal IO via FFI, to keep the demo free of universe-level noise.
infixl 1 _>>_
postulate
  putStrLn : String → IO ⊤
  _>>_     : IO ⊤ → IO ⊤ → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# COMPILE GHC putStrLn = TIO.putStrLn #-}
{-# COMPILE GHC _>>_ = (>>) #-}

-- demo data: 4 validators, one Byzantine liar (999999) — mirrors the
-- Haskell node's first round so the proven kernel and the demo tell one
-- story with the same numbers.
clocks : List Nat
clocks = 1000 ∷ 1001 ∷ 1002 ∷ 999999 ∷ []

-- all 4 validators signed; a quorum for n=4, f=1 needs n−f = 3.
signers : List Bool
signers = true ∷ true ∷ true ∷ true ∷ []

-- a contract:  if (2 ≤ 3) then 7*6 else 0   ⇒ 42
demoContract : Expr
demoContract = ite (leq (lit 2) (lit 3)) (mul (lit 7) (lit 6)) (lit 0)

main =
      putStrLn ("Sanctum kernel self-test (extracted from Agda)")
   >> putStrLn ("  median block time = " ++ show (medianTime clocks)
                ++ "  (Byzantine 999999 rejected)")
   >> putStrLn ("  quorum reached (n=4,f=1) = " ++ showBool (quorumReached 4 1 signers))
   >> putStrLn ("  contract result = " ++ show (runContract demoContract))
