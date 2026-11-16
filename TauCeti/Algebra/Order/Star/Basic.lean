/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Products of nonnegative elements in commutative star-ordered rings

In a general (noncommutative) `StarOrderedRing`, a product of two nonnegative elements need not be
nonnegative. When the ring is commutative, `StarMul.toStarModule` gives `StarModule R R` and hence
`IsOrderedModule R R`, so products (`StarOrderedRing.mul_nonneg`) — and by induction finite products
over any `Finset` (`Finset.prod_nonneg_of_starOrderedRing`) — of nonnegative elements remain
nonnegative.
-/

public section

namespace StarOrderedRing

/-- In a commutative `StarOrderedRing`, the product of two nonnegative elements is nonnegative. -/
theorem mul_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  smul_nonneg ha hb

end StarOrderedRing

namespace Finset

/-- A finite product of nonnegative elements in a commutative `StarOrderedRing` is nonnegative. -/
theorem prod_nonneg_of_starOrderedRing {ι R : Type*} [CommSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {s : Finset ι} {f : ι → R}
    (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i :=
  prod_induction f (0 ≤ ·) (fun _ _ ha hb ↦ StarOrderedRing.mul_nonneg ha hb) zero_le_one hf

end Finset
