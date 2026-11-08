/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights

/-!
# Bounding a linear form on a box

A linear form `∑ i ∈ s, x i * c i` with coefficients `|c i| ≤ A` evaluated at a point with
coordinates `|x i| ≤ B` has absolute value at most `#s * (B * A)`. This is the size estimate for
the values of a linear form on a box, as in the pigeonhole argument for Siegel's lemma.

## Main results

* `Finset.abs_sum_mul_le_card_mul_mul`: the bound `|∑ i ∈ s, x i * c i| ≤ #s * (B * A)`.
-/

public section

namespace Finset

variable {ι R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]

/-- A linear form with coefficients of absolute value at most `A`, evaluated at a point whose
coordinates have absolute value at most `B`, has absolute value at most `#s * (B * A)`. -/
theorem abs_sum_mul_le_card_mul_mul {s : Finset ι} {x c : ι → R} {A B : R}
    (hc : ∀ i ∈ s, |c i| ≤ A) (hx : ∀ i ∈ s, |x i| ≤ B) :
    |∑ i ∈ s, x i * c i| ≤ #s * (B * A) := by
  simpa only [nsmul_eq_mul] using abs_sum_le_card_nsmul (B := B * A) fun i hi ↦ by
    rw [abs_mul]
    exact mul_le_mul (hx i hi) (hc i hi) (abs_nonneg _) ((abs_nonneg _).trans (hx i hi))

end Finset
