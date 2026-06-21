------------------------------------------------------------------------
-- Principle 6 · Perfection, Harmony  (time component)
--
-- BFT TIME SOUNDNESS.
--
-- A block carries no external timestamp authority.  Instead its time is
-- the MEDIAN of the clocks of the ≥ 2f+1 validators that signed it.
-- We prove: if more than f of those validators are honest and their
-- clocks all lie within [lo,hi], then the median also lies in [lo,hi].
--
-- Hence a finalised timestamp is bounded by honest reality — even with
-- f Byzantine validators lying arbitrarily about the time.  This is what
-- lets a hospital trust "this signature existed at time T" without any
-- trusted clock and without contacting the outside world.
--
-- The median is characterised by its defining property (≥ f+1 samples
-- below-or-equal and ≥ f+1 above-or-equal), so no sorting machinery is
-- needed; any value with that property — in particular the real median
-- of 2f+1 samples — is bounded.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.Proofs.Time where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Vec using (Vec; map; lookup)
open import Data.Vec.Properties using (lookup-map)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality

open import Sanctum.Proofs.Counting

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- A boolean ≤ test on naturals, with the two facts we need.

leb : ℕ → ℕ → Bool
leb zero    _       = true
leb (suc _) zero    = false
leb (suc a) (suc b) = leb a b

leb-true : ∀ {a b} → leb a b ≡ true → a ≤ b
leb-true {zero}            _ = z≤n
leb-true {suc a} {suc b}   p = s≤s (leb-true p)

-- if a ≤ b is false then b < a
leb-false : ∀ {a b} → leb a b ≡ false → b < a
leb-false {suc a} {zero}  _ = s≤s z≤n
leb-false {suc a} {suc b} p = s≤s (leb-false p)

-- a strict order makes the ≤ test false
<→leb-false : ∀ {a b} → b < a → leb a b ≡ false
<→leb-false {suc a} {zero}  _         = refl
<→leb-false {suc a} {suc b} (s≤s b<a) = <→leb-false b<a

------------------------------------------------------------------------
-- The sample sets "below-or-equal m" and "above-or-equal m".

belowEq : ℕ → Vec ℕ n → Vec Bool n
belowEq m = map (λ t → leb t m)

aboveEq : ℕ → Vec ℕ n → Vec Bool n
aboveEq m = map (λ t → leb m t)

-- m is a median of the samples: at least f+1 lie at-or-below it and at
-- least f+1 lie at-or-above it.
record IsMedian (f m : ℕ) (samples : Vec ℕ n) : Set where
  field
    below≥ : f + 1 ≤ count (belowEq m samples)
    above≥ : f + 1 ≤ count (aboveEq m samples)

module _ (f : ℕ) where

  private
    twice : (f + 1) + (f + 1) ≡ suc (2 * f + 1)
    twice = go f
      where
        open import Data.Nat.Solver using (module +-*-Solver)
        open +-*-Solver
        go : ∀ g → (g + 1) + (g + 1) ≡ suc (2 * g + 1)
        go = solve 1 (λ x → (x :+ con 1) :+ (x :+ con 1)
                          := con 1 :+ (con 2 :* x :+ con 1)) refl

  ----------------------------------------------------------------------
  -- Generic clash: two sets of size ≥ f+1 inside a set of size ≤ 2f+1
  -- that are disjoint cannot coexist.

  quorum-clash :
    (P h : Vec Bool n) →
    n ≤ 2 * f + 1 →
    f + 1 ≤ count P →
    f + 1 ≤ count h →
    (∀ i → lookup h i ≡ true → lookup P i ≡ false) →
    ⊥
  quorum-clash {n} P h n≤ cP ch disjoint = <-irrefl refl clash
    where
      empties : ∀ i → lookup (P ∩ h) i ≡ false
      empties i with lookup h i in eq
      ... | true  = trans (lookup-∩ P h i)
                          (trans (cong (_∧ lookup h i) (disjoint i eq))
                                 refl)
      ... | false = trans (lookup-∩ P h i)
                          (trans (cong (lookup P i ∧_) eq)
                                 (∧-zeroʳ (lookup P i)))

      P∩h≡0 : count (P ∩ h) ≡ 0
      P∩h≡0 = allFalse→count0 (P ∩ h) empties

      bound : count P + count h ≤ n            -- |P| + |h| ≤ n + 0 = n
      bound = subst (count P + count h ≤_)
                (trans (cong (n +_) P∩h≡0) (+-identityʳ n))
                (ie-bound P h)

      big : (f + 1) + (f + 1) ≤ n
      big = ≤-trans (+-mono-≤ cP ch) bound

      clash : suc (2 * f + 1) ≤ 2 * f + 1
      clash = ≤-trans (subst (_≤ n) twice big) n≤

  ----------------------------------------------------------------------
  -- MAIN THEOREM · the median lies within the honest clock interval.

  median-bound :
    {lo hi : ℕ} {m : ℕ} {ts : Vec ℕ n} (h : Vec Bool n) →
    n ≤ 2 * f + 1 →
    f + 1 ≤ count h →
    IsMedian f m ts →
    (∀ i → lookup h i ≡ true → lo ≤ lookup ts i) →     -- honest clocks ≥ lo
    (∀ i → lookup h i ≡ true → lookup ts i ≤ hi) →     -- honest clocks ≤ hi
    (lo ≤ m) × (m ≤ hi)
  median-bound {lo = lo} {hi = hi} {m = m} {ts = ts} h n≤ ch med lo≤ ≤hi =
    lo≤m , m≤hi
    where
      open IsMedian med

      ----------------------------------------------------------------
      -- m ≤ hi : otherwise every honest clock is < m, so the honest set
      -- is disjoint from `aboveEq m`, contradicting both having ≥ f+1.
      m≤hi : m ≤ hi
      m≤hi with m ≤? hi
      ... | yes p = p
      ... | no ¬p =
        ⊥-elim (quorum-clash (aboveEq m ts) h n≤ above≥ ch dis)
        where
          hi<m : hi < m
          hi<m = ≰⇒> ¬p
          dis : ∀ i → lookup h i ≡ true → lookup (aboveEq m ts) i ≡ false
          dis i hi′ =
            trans (lookup-map i (λ t → leb m t) ts)
                  (<→leb-false (<-transʳ (≤hi i hi′) hi<m))

      ----------------------------------------------------------------
      -- lo ≤ m : symmetric, using `belowEq m`.
      lo≤m : lo ≤ m
      lo≤m with lo ≤? m
      ... | yes p = p
      ... | no ¬p =
        ⊥-elim (quorum-clash (belowEq m ts) h n≤ below≥ ch dis)
        where
          m<lo : m < lo
          m<lo = ≰⇒> ¬p
          dis : ∀ i → lookup h i ≡ true → lookup (belowEq m ts) i ≡ false
          dis i hi′ =
            trans (lookup-map i (λ t → leb t m) ts)
                  (<→leb-false (<-transˡ m<lo (lo≤ i hi′)))
