------------------------------------------------------------------------
-- Principle 0 · Pustka / Void
--
-- The empty, from which everything is born.  Before there is any fact,
-- any identity, any history, there is only the void: the empty octet
-- string and the zero hash that stands for "nothing" — the parent of
-- genesis.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.P0_Void where

open import Data.Nat using (ℕ; zero) public
open import Data.List using (List; []) public

-- An opaque octet string.  (In the running node this is a ByteString;
-- in the model its internal structure is irrelevant.)
Bytes : Set
Bytes = List ℕ

-- A cryptographic digest, modelled as an opaque identifier.  The proofs
-- treat it abstractly; the node computes real BLAKE2b/SHA-256 digests.
Hash : Set
Hash = ℕ

-- The void.
∅ᵇ : Bytes
∅ᵇ = []

-- The hash of the void: the parent of genesis, the bottom of every chain.
zeroHash : Hash
zeroHash = zero
