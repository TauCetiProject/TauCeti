/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Bates.Basic
public import TauCeti.Probability.Distributions.IrwinHall.Support

/-!
# Support of Bates laws

A Bates law of positive order is the average of a nonempty finite family of unit-uniform
variables, so its topological support is the closed unit interval. At order zero the Bates law is
the zero measure and has empty support.

The result transports the exact Irwin–Hall support through the positive scaling from a sum to an
average.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The topological support of a positive-order Bates law is `[0, 1]`; at order zero it is
empty because the totalized law is the zero measure. -/
@[simp]
theorem support_batesMeasure (n : ℕ) :
    (batesMeasure n).support = if n = 0 then ∅ else Icc (0 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [ite_eq_right hn.ne', batesMeasure_eq_map_irwinHallMeasure hn]
  have hfun : (fun x : ℝ ↦ x / (n : ℝ)) = fun x ↦ 0 + (n : ℝ)⁻¹ * x := by
    funext x
    simp [div_eq_mul_inv, mul_comm]
  rw [hfun]
  rw [support_map_affine (inv_ne_zero (ne_of_gt hnR)), support_irwinHallMeasure]
  simpa [add_comm, hnR.ne'] using
    (image_affine_Icc' (a := (n : ℝ)⁻¹) (inv_pos.mpr hnR) (0 : ℝ) 0 (n : ℝ))

end TauCeti.Probability
