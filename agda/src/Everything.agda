------------------------------------------------------------------------
-- Sanctum — type-check entry point.
--
--   agda src/Everything.agda
--
-- checks every module: the seven principles (P0–P6), the machine-checked
-- theses (Sanctum.Proofs.*), and the extractable kernel.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Everything where

-- The seven holy principles.
open import Sanctum.P0_Void
open import Sanctum.P1_Truth
open import Sanctum.P2_Distinction
open import Sanctum.P3_Connection
open import Sanctum.P4_Structure
open import Sanctum.P5_Life
open import Sanctum.P6_Harmony

-- The theses.
open import Sanctum.Proofs.Counting
open import Sanctum.Proofs.Quorum
open import Sanctum.Proofs.Time
open import Sanctum.Proofs.Append
open import Sanctum.Proofs.Totality

-- The extractable executable kernel.
open import Sanctum.Kernel
