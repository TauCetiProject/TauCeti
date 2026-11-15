/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# The chordal distance on `ℂ`

The **chordal distance** `Complex.chordalDist z w = ‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))`
is the Euclidean distance between the images of `z` and `w` under stereographic projection onto
the sphere of diameter one resting on the plane at `0`. It is a metric on `ℂ` bounded by one in
which points of large modulus are close: `chordalDist R (-R) = 2 R / (1 + R ^ 2)` tends to zero
as `R → ∞`, so a sequence of sets may escape to `∞` while its chordal diameters tend to zero. On
a bounded set it is comparable with the Euclidean distance.

## Main declarations

* `Complex.chordalDist` -- the chordal distance, with its formula `Complex.chordalDist_def`.
* `Complex.chordalDist_self`, `Complex.chordalDist_comm`, `Complex.chordalDist_nonneg`,
  `Complex.chordalDist_eq_zero`, `Complex.chordalDist_triangle` -- the axioms of a metric.
* `Complex.chordalDist_le_one` -- the chordal distance is at most one.
* `Complex.chordalDist_le_norm_sub`, `Complex.norm_sub_le_mul_chordalDist`,
  `Complex.norm_sub_lt_of_chordalDist_lt` -- on a bounded set, chordal and Euclidean distances are
  comparable.

## Implementation notes

The triangle inequality is proved by writing the stereographic projection as the inversion of
`ℂ × ℝ` (with its Euclidean norm) in the unit sphere about `(0, 1)`, whose effect on distances is
Mathlib's `EuclideanGeometry.dist_inversion_inversion`.

## References

* L. V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 1, Section 2.4, which projects onto the
  unit sphere and so obtains twice this distance.
-/

public section

noncomputable section

namespace Complex

/-- The **chordal distance** `‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))` between two complex
numbers: the Euclidean distance between their images under stereographic projection onto the
sphere of diameter one resting on the plane at `0`. It is at most one
(`Complex.chordalDist_le_one`), and two points of large modulus are chordally close. -/
def chordalDist (z w : ℂ) : ℝ :=
  ‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))

/-- The formula defining the chordal distance. -/
theorem chordalDist_def (z w : ℂ) :
    chordalDist z w = ‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) :=
  (rfl)

/-- The denominator of the chordal distance is positive. -/
private theorem sqrt_one_add_sq_mul_pos (z w : ℂ) : 0 < √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) :=
  Real.sqrt_pos.mpr (by positivity)

/-- A point is at chordal distance zero from itself. -/
@[simp]
theorem chordalDist_self (z : ℂ) : chordalDist z z = 0 := by
  simp [chordalDist_def]

/-- The chordal distance is symmetric. -/
theorem chordalDist_comm (z w : ℂ) : chordalDist z w = chordalDist w z := by
  rw [chordalDist_def, chordalDist_def, norm_sub_rev, mul_comm (1 + ‖z‖ ^ 2)]

/-- The chordal distance is nonnegative. -/
@[simp]
theorem chordalDist_nonneg (z w : ℂ) : 0 ≤ chordalDist z w := by
  rw [chordalDist_def]
  positivity

/-- Two points are at chordal distance zero exactly when they are equal. -/
@[simp]
theorem chordalDist_eq_zero {z w : ℂ} : chordalDist z w = 0 ↔ z = w := by
  rw [chordalDist_def, div_eq_zero_iff, or_iff_left (sqrt_one_add_sq_mul_pos z w).ne', norm_eq_zero,
    sub_eq_zero]

/-- The **triangle inequality** for the chordal distance. -/
theorem chordalDist_triangle (z u w : ℂ) :
    chordalDist z w ≤ chordalDist z u + chordalDist u w := by
  -- Stereographic projection is the inversion of `ℂ × ℝ` in the unit sphere about `(0, 1)`, which
  -- divides the distance of two points of the plane by the product of their distances to `(0, 1)`.
  let ι (a : ℂ) : WithLp 2 (ℂ × ℝ) := WithLp.toLp 2 (a, 0)
  let N : WithLp 2 (ℂ × ℝ) := WithLp.toLp 2 (0, 1)
  have hN (a : ℂ) : ι a ≠ N := fun h => zero_ne_one congr((WithLp.ofLp $h).2)
  have hdist (a b : ℂ) : dist (ι a) (ι b) = ‖a - b‖ := by
    rw [WithLp.prod_dist_eq_of_L2]
    simp [ι, dist_eq_norm]
  have hdistN (a : ℂ) : dist (ι a) N = √(1 + ‖a‖ ^ 2) := by
    simp [ι, N, WithLp.prod_dist_eq_of_L2, add_comm]
  have key (a b : ℂ) : chordalDist a b =
      dist (EuclideanGeometry.inversion N 1 (ι a)) (EuclideanGeometry.inversion N 1 (ι b)) := by
    rw [EuclideanGeometry.dist_inversion_inversion (hN a) (hN b), hdist, hdistN, hdistN,
      chordalDist_def, Real.sqrt_mul (by positivity)]
    ring
  rw [key z w, key z u, key u w]
  exact dist_triangle _ _ _

/-- The chordal distance is at most one. -/
theorem chordalDist_le_one (z w : ℂ) : chordalDist z w ≤ 1 := by
  rw [chordalDist_def, div_le_one (sqrt_one_add_sq_mul_pos z w),
    Real.le_sqrt (norm_nonneg _) (by positivity)]
  have h := norm_sub_le z w
  nlinarith [norm_nonneg z, norm_nonneg w, norm_nonneg (z - w), sq_nonneg (‖z‖ * ‖w‖ - 1)]

/-- The chordal distance is at most the Euclidean distance. -/
theorem chordalDist_le_norm_sub (z w : ℂ) : chordalDist z w ≤ ‖z - w‖ := by
  rw [chordalDist_def]
  exact div_le_self (norm_nonneg _)
    (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖w‖]))

/-- On the closed disc of radius `R` about `0`, the Euclidean distance is at most `1 + R ^ 2`
times the chordal distance. -/
theorem norm_sub_le_mul_chordalDist {R : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖z - w‖ ≤ (1 + R ^ 2) * chordalDist z w := by
  have hs : √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) ≤ 1 + R ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖w‖]
  rw [chordalDist_def, mul_div_assoc', le_div_iff₀ (sqrt_one_add_sq_mul_pos z w)]
  nlinarith [norm_nonneg (z - w)]

/-- On the closed disc of radius `R` about `0`, a chordal distance below `ε / (1 + R ^ 2)` forces
a Euclidean distance below `ε`. -/
theorem norm_sub_lt_of_chordalDist_lt {R ε : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R)
    (h : chordalDist z w < ε / (1 + R ^ 2)) : ‖z - w‖ < ε :=
  calc
    ‖z - w‖ ≤ (1 + R ^ 2) * chordalDist z w := norm_sub_le_mul_chordalDist hz hw
    _ < (1 + R ^ 2) * (ε / (1 + R ^ 2)) := mul_lt_mul_of_pos_left h (by positivity)
    _ = ε := by field_simp

end Complex

end
