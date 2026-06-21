------------------------------------------------------------------------
-- Shared combinatorial toolkit for the BFT proofs.
--
-- Subsets of an n-element validator set are characteristic vectors
-- `Vec Bool n`.  `count` is their cardinality.  Everything here is
-- elementary induction on vectors — no axioms — and is reused by both
-- the quorum-intersection proof (Principle 5) and the median-time
-- proof (Principle 6).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Sanctum.Proofs.Counting where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Vec using (Vec; []; _∷_; zipWith; map; lookup)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality

private
  variable
    n : ℕ

-- Cardinality of a subset.
count : Vec Bool n → ℕ
count []           = 0
count (true  ∷ xs) = suc (count xs)
count (false ∷ xs) = count xs

-- Intersection (pointwise ∧) and complement (pointwise not).
_∩_ : Vec Bool n → Vec Bool n → Vec Bool n
_∩_ = zipWith _∧_

infixr 6 _∩_

∁ : Vec Bool n → Vec Bool n
∁ = map not

------------------------------------------------------------------------
-- Bool / lookup helpers.

and-elimˡ : ∀ {x y} → x ∧ y ≡ true → x ≡ true
and-elimˡ {true} _ = refl

and-elimʳ : ∀ {x y} → x ∧ y ≡ true → y ≡ true
and-elimʳ {true} {true} _ = refl

lookup-∩ : (a b : Vec Bool n) (i : Fin n) →
           lookup (a ∩ b) i ≡ lookup a i ∧ lookup b i
lookup-∩ (a ∷ _)  (b ∷ _)  zero    = refl
lookup-∩ (_ ∷ as) (_ ∷ bs) (suc i) = lookup-∩ as bs i

------------------------------------------------------------------------
-- Core cardinality facts.

-- |A ∩ B| ≤ |B|.
count-∩-≤ʳ : (a b : Vec Bool n) → count (a ∩ b) ≤ count b
count-∩-≤ʳ []           []           = z≤n
count-∩-≤ʳ (true  ∷ as) (true  ∷ bs) = s≤s (count-∩-≤ʳ as bs)
count-∩-≤ʳ (true  ∷ as) (false ∷ bs) = count-∩-≤ʳ as bs
count-∩-≤ʳ (false ∷ as) (true  ∷ bs) = ≤-step (count-∩-≤ʳ as bs)
count-∩-≤ʳ (false ∷ as) (false ∷ bs) = count-∩-≤ʳ as bs

-- Inclusion–exclusion:  |A| + |B| ≤ n + |A ∩ B|.
ie-bound : (a b : Vec Bool n) → count a + count b ≤ n + count (a ∩ b)
ie-bound []           []           = z≤n
ie-bound {suc n} (true  ∷ as) (true  ∷ bs)
  rewrite +-suc (count as) (count bs) | +-suc n (count (as ∩ bs))
  = s≤s (s≤s (ie-bound as bs))
ie-bound (true  ∷ as) (false ∷ bs) = s≤s (ie-bound as bs)
ie-bound {suc n} (false ∷ as) (true ∷ bs)
  rewrite +-suc (count as) (count bs) = s≤s (ie-bound as bs)
ie-bound (false ∷ as) (false ∷ bs) = ≤-step (ie-bound as bs)

-- |V| = |V ∩ H| + |V ∩ ∁H|.
count-split : (v h : Vec Bool n) → count v ≡ count (v ∩ h) + count (v ∩ ∁ h)
count-split []           []           = refl
count-split (false ∷ vs) (_     ∷ hs) = count-split vs hs
count-split (true  ∷ vs) (true  ∷ hs) = cong suc (count-split vs hs)
count-split (true  ∷ vs) (false ∷ hs)
  rewrite count-split vs hs =
    sym (+-suc (count (vs ∩ hs)) (count (vs ∩ ∁ hs)))

-- A positive count yields a concrete index witness.
positive→witness : (v : Vec Bool n) → 0 < count v → ∃[ i ] lookup v i ≡ true
positive→witness (true  ∷ vs) _   = zero , refl
positive→witness (false ∷ vs) 0<c with positive→witness vs 0<c
... | i , p = suc i , p

-- An everywhere-false subset is empty.
allFalse→count0 : (v : Vec Bool n) → (∀ i → lookup v i ≡ false) → count v ≡ 0
allFalse→count0 []           _ = refl
allFalse→count0 (false ∷ vs) p = allFalse→count0 vs (λ i → p (suc i))
allFalse→count0 (true  ∷ vs) p with p zero
... | ()
