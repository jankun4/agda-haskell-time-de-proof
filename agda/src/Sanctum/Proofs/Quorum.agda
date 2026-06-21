------------------------------------------------------------------------
-- Principle 5 · Life, Rebellion, Resistance
--
-- The heart of Byzantine resistance: QUORUM INTERSECTION.
--
-- A validator set of n members tolerates up to f Byzantine faults when
-- n ≤ 3f+1 and every decision needs a quorum of ≥ 2f+1 signatures.
-- We prove that any two such quorums must share at least one *honest*
-- member.  From this, Agreement follows: two conflicting blocks can
-- never both gather a quorum, so distrusting hospitals still converge
-- on one history.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.Proofs.Quorum where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Vec using (Vec; lookup)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality

open import Sanctum.Proofs.Counting

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- MAIN THEOREM · A quorum intersection contains an honest validator.

module _ (f : ℕ) where

  -- A quorum needs at least 2f+1 signatures.
  QuorumThreshold : ℕ
  QuorumThreshold = 2 * f + 1

  -- Arithmetic core, discharged by the ring solver.
  private
    sizes : (2 * f + 1) + (2 * f + 1) ≡ (3 * f + 1) + (f + 1)
    sizes = go f
      where
        open import Data.Nat.Solver using (module +-*-Solver)
        open +-*-Solver
        go : ∀ g → (2 * g + 1) + (2 * g + 1) ≡ (3 * g + 1) + (g + 1)
        go = solve 1
          (λ x → (con 2 :* x :+ con 1) :+ (con 2 :* x :+ con 1)
               := (con 3 :* x :+ con 1) :+ (x :+ con 1))
          refl

  quorum-intersection-honest :
    (a b h : Vec Bool n) →
    n ≤ 3 * f + 1 →                 -- fault assumption: n ≤ 3f+1
    QuorumThreshold ≤ count a →     -- a is a quorum
    QuorumThreshold ≤ count b →     -- b is a quorum
    count (∁ h) ≤ f →               -- at most f dishonest
    ∃[ i ] (lookup a i ≡ true × lookup b i ≡ true × lookup h i ≡ true)
  quorum-intersection-honest {n} a b h n≤3f+1 qa qb d≤f = result
    where
      cab  = count (a ∩ b)
      cg   = count ((a ∩ b) ∩ h)
      cd'  = count ((a ∩ b) ∩ ∁ h)

      -- |a ∩ b| ≥ f+1
      sum≥ : (2 * f + 1) + (2 * f + 1) ≤ count a + count b
      sum≥ = +-mono-≤ qa qb

      chain : (3 * f + 1) + (f + 1) ≤ (3 * f + 1) + cab
      chain = subst (_≤ (3 * f + 1) + cab) sizes
               (≤-trans sum≥
                 (≤-trans (ie-bound a b)
                          (+-monoˡ-≤ cab n≤3f+1)))

      ab≥f+1 : f + 1 ≤ cab
      ab≥f+1 = +-cancelˡ-≤ (3 * f + 1) chain

      -- |(a ∩ b) ∩ h| ≥ 1
      split : cab ≡ cg + cd'
      split = count-split (a ∩ b) h

      d'≤f : cd' ≤ f
      d'≤f = ≤-trans (count-∩-≤ʳ (a ∩ b) (∁ h)) d≤f

      f+1≤cg+f : f + 1 ≤ cg + f
      f+1≤cg+f = ≤-trans (subst (f + 1 ≤_) split ab≥f+1)
                         (+-monoʳ-≤ cg d'≤f)

      pos : 1 ≤ cg
      pos = +-cancelˡ-≤ f (subst (f + 1 ≤_) (+-comm cg f) f+1≤cg+f)

      -- extract and decompose the witness
      wit : ∃[ i ] lookup ((a ∩ b) ∩ h) i ≡ true
      wit = positive→witness ((a ∩ b) ∩ h) pos

      result : ∃[ i ] (lookup a i ≡ true × lookup b i ≡ true × lookup h i ≡ true)
      result with wit
      ... | i , p =
        let p₁ : lookup (a ∩ b) i ∧ lookup h i ≡ true
            p₁ = trans (sym (lookup-∩ (a ∩ b) h i)) p
            pab : lookup (a ∩ b) i ≡ true
            pab = and-elimˡ p₁
            ph  : lookup h i ≡ true
            ph  = and-elimʳ p₁
            p₂ : lookup a i ∧ lookup b i ≡ true
            p₂ = trans (sym (lookup-∩ a b i)) pab
        in i , and-elimˡ p₂ , and-elimʳ p₂ , ph

-- The operational Agreement corollary (no two conflicting blocks can both
-- be finalised at one height) is stated over concrete blocks and quorum
-- certificates in `Sanctum.P6_Harmony`, on top of this theorem.
