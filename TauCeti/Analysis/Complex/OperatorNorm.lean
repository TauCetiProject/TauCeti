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
estimate turns a Cauchy--Riemann equation into a bound on the full differential.
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

end ContinuousLinearMap

end
