------------------------------------------------------------------------
-- Principle 4 · Structure   and   Principle 5 · Life (growth)
--
-- Two structural theses:
--
--  (A) APPEND-ONLY.  The ledger only ever grows.  Extending a chain
--      preserves every earlier block at its original position — history
--      can never be rewritten.  (`prefix-preserves`)
--
--  (B) RECONFIGURATION SAFETY.  The validator set may change over time
--      (new hospitals join, old ones leave), but a new set is adopted
--      only when the *previous* set approved it.  Hence every authorised
--      validator set has an unbroken approval lineage back to genesis —
--      authority is never created from nothing.  (`authorised→lineage`)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.Proofs.Append where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- (A)  Append-only ledgers.

module AppendOnly (Block : Set) where

  -- A chain grows by snoc; genesis is the empty root.
  data Chain : Set where
    genesis : Chain
    _▸_     : Chain → Block → Chain

  infixl 5 _▸_

  height : Chain → ℕ
  height genesis = zero
  height (c ▸ _) = suc (height c)

  -- The block at position i (0 = genesis side).
  blockAt : (c : Chain) → Fin (height c) → Block
  blockAt (c ▸ b) zero    = b
  blockAt (c ▸ b) (suc i) = blockAt c i

  -- c is a prefix of d: d is c extended by zero or more blocks.
  data _≼_ : Chain → Chain → Set where
    refl≼ : ∀ {c}     → c ≼ c
    snoc≼ : ∀ {c d b} → c ≼ d → c ≼ (d ▸ b)

  infix 4 _≼_

  ≼-trans : ∀ {c d e} → c ≼ d → d ≼ e → c ≼ e
  ≼-trans p refl≼       = p
  ≼-trans p (snoc≼ q)   = snoc≼ (≼-trans p q)

  -- Extending always yields a larger chain.
  extend-grows : ∀ c b → c ≼ (c ▸ b)
  extend-grows c b = snoc≼ refl≼

  -- Prefixes never shrink.
  ≼-height : ∀ {c d} → c ≼ d → height c ≤ height d
  ≼-height refl≼     = ≤-refl
    where ≤-refl : ∀ {n} → n ≤ n
          ≤-refl {zero}  = z≤n
          ≤-refl {suc n} = s≤s ≤-refl
  ≼-height (snoc≼ p) = ≤-suc (≼-height p)
    where ≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
          ≤-suc z≤n     = z≤n
          ≤-suc (s≤s p) = s≤s (≤-suc p)

  -- Embed a position of a prefix into the larger chain.
  inject≼ : ∀ {c d} → c ≼ d → Fin (height c) → Fin (height d)
  inject≼ refl≼     i = i
  inject≼ (snoc≼ p) i = suc (inject≼ p i)

  -- THE THEOREM: a prefix's blocks are untouched by later growth.
  -- The block at position i of c is exactly the block at the
  -- corresponding position of any extension d ⊒ c.
  prefix-preserves :
    ∀ {c d} (p : c ≼ d) (i : Fin (height c)) →
    blockAt c i ≡ blockAt d (inject≼ p i)
  prefix-preserves refl≼     i = refl
  prefix-preserves (snoc≼ p) i = prefix-preserves p i

------------------------------------------------------------------------
-- (B)  Reconfiguration safety: chain of authority from genesis.
--
--   Approves old new  :  the set `old` issued a quorum certificate
--                        adopting the next set `new`.

module Reconfiguration
  (VSet     : Set)
  (genesisV : VSet)
  (Approves : VSet → VSet → Set)
  where

  -- A validator set is authorised if it is genesis, or it was adopted by
  -- an already-authorised set.  (This is the *only* way to gain authority.)
  data Authorised : VSet → Set where
    gen  : Authorised genesisV
    step : ∀ {old new} → Authorised old → Approves old new → Authorised new

  -- An explicit certificate lineage from genesis to a set.
  data Lineage : VSet → Set where
    root : Lineage genesisV
    link : ∀ {old new} → Lineage old → Approves old new → Lineage new

  -- THE THEOREM: every authorised validator set has an unbroken approval
  -- lineage back to genesis.  No set is ever authorised out of nothing.
  authorised→lineage : ∀ {vs} → Authorised vs → Lineage vs
  authorised→lineage gen          = root
  authorised→lineage (step a ap)  = link (authorised→lineage a) ap

  -- How many reconfigurations separate a set from genesis.
  generation : ∀ {vs} → Lineage vs → ℕ
  generation root       = zero
  generation (link l _) = suc (generation l)
