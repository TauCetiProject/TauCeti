/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation scaling of the `Lᵖ` seminorm

Dilating the variable of a function on a finite-dimensional real normed space `E` by `r⁻¹`, for
`r > 0`, multiplies its `Lᵖ` seminorm against an additive Haar measure by `r ^ (n / p)`, where
`n` is the dimension of `E`; for `p = 0` and `p = ∞` the factor is `1`. This is the `eLpNorm`
counterpart of the lower Lebesgue integral law `TauCeti.lintegral_comp_inv_smul`.

## Main declarations

* `TauCeti.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {G : Type*} [TopologicalSpace G] [ContinuousENorm G]

/-- **Dilation scaling of the `Lᵖ` seminorm:** `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`, where
`n` is the dimension of the ambient space. For `p = 0` and `p = ∞` the factor is `1`. -/
theorem eLpNorm_comp_inv_smul (u : E → G) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) :
    eLpNorm (fun x => u (r⁻¹ • x)) p μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal)) * eLpNorm u p μ := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  rw [← Function.comp_def, ← (measurableEmbedding_const_smul₀ hr').eLpNorm_map_measure,
    Measure.map_addHaar_smul μ hr', eLpNorm_smul_measure_of_ne_zero (by positivity), smul_eq_mul]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hr.le, one_div, ENNReal.toReal_inv, div_eq_mul_inv]

end TauCeti
