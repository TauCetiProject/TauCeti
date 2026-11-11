/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Second moments of finite Gaussian sums

The Gaussian second moment of a finite family in a real normed space is the square root
of the expected squared norm of its sum with independent standard Gaussian coefficients.
The coefficient space is the native Euclidean space with its standard Gaussian measure.
In particular the definition works for empty families and does not require completeness
of the target space.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

variable {ι Y : Type*} [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A finite Gaussian sum has every finite moment, even in an incomplete target. -/
theorem memLp_gaussianSum (x : ι → Y) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • x i) p
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let T : EuclideanSpace ℝ ι →L[ℝ] Y :=
    ∑ i, (EuclideanSpace.proj i).smulRight (x i)
  simpa only [T, Function.comp_def, id_eq, sum_apply,
    ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj] using
    T.comp_memLp' (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) p hp)

/-- The squared norm of a finite Gaussian sum is integrable. -/
theorem integrable_norm_sq_gaussianSum (x : ι → Y) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, g i • x i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  (memLp_gaussianSum x 2 (by simp)).integrable_norm_pow (by norm_num)

/-- The Gaussian second moment of a finite family, with independent real standard Gaussian
coefficients. -/
def gaussianSecondMoment (x : ι → Y) : ℝ :=
  √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι))

/-- The defining integral of the Gaussian second moment. -/
theorem gaussianSecondMoment_def (x : ι → Y) :
    gaussianSecondMoment x =
      √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)) :=
  (rfl)

/-- Gaussian second moments are nonnegative. -/
theorem gaussianSecondMoment_nonneg (x : ι → Y) : 0 ≤ gaussianSecondMoment x :=
  Real.sqrt_nonneg _

/-- Squaring the Gaussian second moment recovers the expected squared norm. -/
theorem gaussianSecondMoment_sq (x : ι → Y) :
    gaussianSecondMoment x ^ 2 =
      ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) :=
  Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)

/-- Multiplying a family by a real scalar multiplies its Gaussian second moment by the
absolute value of that scalar. -/
theorem gaussianSecondMoment_smul (x : ι → Y) (c : ℝ) :
    gaussianSecondMoment (fun i ↦ c • x i) = |c| * gaussianSecondMoment x := by
  have hs (g : EuclideanSpace ℝ ι) :
      (∑ i, g i • (c • x i)) = c • ∑ i, g i • x i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
  apply (sq_eq_sq₀ (gaussianSecondMoment_nonneg _)
    (mul_nonneg (abs_nonneg _) (gaussianSecondMoment_nonneg _))).1
  rw [mul_pow, gaussianSecondMoment_sq, gaussianSecondMoment_sq]
  simp_rw [hs, norm_smul, mul_pow]
  rw [integral_const_mul, Real.norm_eq_abs]

@[simp]
theorem gaussianSecondMoment_zero : gaussianSecondMoment (0 : ι → Y) = 0 := by
  simp [gaussianSecondMoment]

/-- An empty Gaussian sum has second moment zero. -/
@[simp]
theorem gaussianSecondMoment_of_isEmpty [IsEmpty ι] (x : ι → Y) :
    gaussianSecondMoment x = 0 := by
  simp [gaussianSecondMoment]

end TauCeti
