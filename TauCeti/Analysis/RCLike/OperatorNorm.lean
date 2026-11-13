/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Bounds for real-linear maps out of an `RCLike` field

A continuous real-linear map `L` out of an `RCLike` field `K` is determined by its values on `1`
and `I`, and these control its norm: `‖L z‖ ≤ (‖L 1‖ + ‖L I‖) * ‖z‖`
(`ContinuousLinearMap.norm_apply_le_norm_one_add_norm_I`). This estimate turns a Cauchy--Riemann
equation into a bound on the full differential: if `L I = A (L 1)` with `‖A‖ ≤ M`, then
`‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖` (`ContinuousLinearMap.norm_apply_le_of_apply_I_eq`); with
`‖L 1‖ ≤ B` this bounds the operator norm by `(1 + M) * B`
(`ContinuousLinearMap.norm_le_of_apply_I_eq`).

For `K = ℝ` the imaginary unit is `0` and the first bound reduces to `‖L z‖ ≤ ‖L 1‖ * ‖z‖`; the
other two keep their factor `1 + M`.
-/

public section

namespace ContinuousLinearMap

variable {K V : Type*} [RCLike K] [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Bound a real-linear map on a vector of an `RCLike` field by its values on `1` and `I`. -/
theorem norm_apply_le_norm_one_add_norm_I (L : K →L[ℝ] V) (z : K) :
    ‖L z‖ ≤ (‖L 1‖ + ‖L RCLike.I‖) * ‖z‖ := by
  have hz : L z = RCLike.re z • L 1 + RCLike.im z • L RCLike.I := by
    conv_lhs => rw [← RCLike.re_add_im z]
    simp [RCLike.ofReal_alg]
  rw [hz, add_mul]
  grw [norm_add_le, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    RCLike.abs_re_le_norm, RCLike.abs_im_le_norm]
  simp [mul_comm]

/-- If a real-linear map out of an `RCLike` field sends `I` to `A (L 1)`, where `‖A‖ ≤ M`, then
`L 1` controls `L`: `‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖`. -/
theorem norm_apply_le_of_apply_I_eq {L : K →L[ℝ] V} {A : V →L[ℝ] V} {M : ℝ}
    (hL : L RCLike.I = A (L 1)) (hA : ‖A‖ ≤ M) (a : K) : ‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖ := by
  grw [L.norm_apply_le_norm_one_add_norm_I a, hL, A.le_of_opNorm_le hA (L 1)]
  exact le_of_eq (by ring)

/-- **Cauchy--Riemann bound.** If a real-linear map `f : K → V` out of an `RCLike` field satisfies
`f I = L (f 1)` with `‖L‖ ≤ M`, and `‖f 1‖ ≤ B`, then `‖f‖ ≤ (1 + M) * B`. -/
theorem norm_le_of_apply_I_eq (f : K →L[ℝ] V) {L : V →L[ℝ] V} {M B : ℝ}
    (hCR : f RCLike.I = L (f 1)) (hL : ‖L‖ ≤ M) (hreal : ‖f 1‖ ≤ B) : ‖f‖ ≤ (1 + M) * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hreal
  have hM : 0 ≤ M := (norm_nonneg _).trans hL
  refine opNorm_le_bound _ (by positivity) fun w ↦ ?_
  grw [norm_apply_le_of_apply_I_eq hCR hL w, hreal]

end ContinuousLinearMap

end
