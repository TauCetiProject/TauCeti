/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Bounds for real-linear maps out of the complex line

The values on `1` and `I` determine a continuous real-linear map on every complex vector
(`ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I`), and control its norm there. This
estimate turns a Cauchy--Riemann equation into a bound on the full differential: if
`L I = A (L 1)` with `‖A‖ ≤ M`, then `‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖`
(`ContinuousLinearMap.norm_apply_le_of_apply_I_eq`); with `‖L 1‖ ≤ B` this bounds the operator norm
by `(1 + M) * B` (`ContinuousLinearMap.norm_le_of_apply_I_eq`).
A real-linear map is the sum of its values at `1` and `I` weighted by the real and imaginary
parts (`ContinuousLinearMap.eq_reCLM_smulRight_add_imCLM_smulRight`, and for families
`ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM`).
-/

public section

namespace ContinuousLinearMap

/-- A continuous real-linear map out of the complex plane is evaluated in the real basis
`(1,I)`. -/
theorem apply_eq_re_smul_one_add_im_smul_I {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] (L : ℂ →L[ℝ] F) (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I :=
  L.toLinearMap.apply_eq_re_smul_one_add_im_smul_I z

/-- Bound a real-linear map on a complex vector by its values on the standard real basis. -/
theorem norm_apply_le_norm_one_add_norm_I {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) (z : ℂ) :
    ‖L z‖ ≤ (‖L 1‖ + ‖L Complex.I‖) * ‖z‖ := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul]
  calc
    ‖L z‖ = ‖z.re • L 1 + z.im • L Complex.I‖ := by
      conv_lhs => rw [hz, map_add, map_smul, map_smul]
    _ ≤ ‖z.re‖ * ‖L 1‖ + ‖z.im‖ * ‖L Complex.I‖ := by
      simpa only [norm_smul] using norm_add_le (z.re • L 1) (z.im • L Complex.I)
    _ ≤ ‖z‖ * ‖L 1‖ + ‖z‖ * ‖L Complex.I‖ := by
      gcongr
      · exact Complex.abs_re_le_norm z
      · exact Complex.abs_im_le_norm z
    _ = (‖L 1‖ + ‖L Complex.I‖) * ‖z‖ := by ring

/-- If a real-linear map out of `ℂ` sends `I` to `A (L 1)`, where `‖A‖ ≤ M`, then `L 1` controls
`L`: `‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖`. -/
theorem norm_apply_le_of_apply_I_eq {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V} {M : ℝ} (hL : L Complex.I = A (L 1)) (hA : ‖A‖ ≤ M)
    (a : ℂ) : ‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖ := by
  refine (L.norm_apply_le_norm_one_add_norm_I a).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg a))
  rw [hL]
  linarith [A.le_of_opNorm_le hA (L 1)]

/-- **Cauchy--Riemann bound.** If a real-linear map `f : ℂ → V` satisfies `f I = L (f 1)` with
`‖L‖ ≤ M`, and `‖f 1‖ ≤ B`, then `‖f‖ ≤ (1 + M) * B`. -/
theorem norm_le_of_apply_I_eq {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℂ →L[ℝ] V) {L : V →L[ℝ] V} {M B : ℝ} (hCR : f Complex.I = L (f 1)) (hL : ‖L‖ ≤ M)
    (hreal : ‖f 1‖ ≤ B) : ‖f‖ ≤ (1 + M) * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hreal
  have hM : 0 ≤ M := (norm_nonneg _).trans hL
  have himag : ‖f Complex.I‖ ≤ M * B := by
    rw [hCR]
    exact (L.le_opNorm _).trans (by gcongr)
  refine opNorm_le_bound _ (by positivity) fun w ↦ ?_
  calc
    ‖f w‖ ≤ (‖f 1‖ + ‖f Complex.I‖) * ‖w‖ := f.norm_apply_le_norm_one_add_norm_I w
    _ ≤ (B + M * B) * ‖w‖ := by gcongr
    _ = (1 + M) * B * ‖w‖ := by ring

/-- A real-linear map out of `ℂ` is determined by its values at `1` and `I`:
`L = re ⬝ L 1 + im ⬝ L I`. -/
theorem eq_reCLM_smulRight_add_imCLM_smulRight {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) :
    L = Complex.reCLM.smulRight (L 1) + Complex.imCLM.smulRight (L Complex.I) := by
  ext z
  simp [L.apply_eq_re_smul_one_add_im_smul_I z]

/-- A family of real-linear maps out of `ℂ` splits through its values at `1` and `I`, written
with the continuous linear maps `smulRightL` so that it can be postcomposed in families. -/
theorem fun_eq_smulRightL_reCLM_add_smulRightL_imCLM {X V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (D : X → ℂ →L[ℝ] V) :
    D = (fun x => smulRightL ℝ ℂ V Complex.reCLM (D x 1)) +
      fun x => smulRightL ℝ ℂ V Complex.imCLM (D x Complex.I) := by
  funext x
  conv_lhs => rw [(D x).eq_reCLM_smulRight_add_imCLM_smulRight]
  ext z
  simp

end ContinuousLinearMap

end
