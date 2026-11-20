/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounding `1 + log x` by a positive power of `x`

For `x ≥ 1` and `δ > 0`, combining `1 ≤ x ^ δ` (`Real.one_le_rpow`) with `log x ≤ x ^ δ / δ`
(`Real.log_le_rpow_div`) bounds `1 + log x` by `(1 + δ⁻¹) * x ^ δ`. This absorbs logarithmic
factors into arbitrarily small powers of `x` in analytic number theory bounds such as Siegel's
theorem.

## Main results

* `Real.one_add_log_le_mul_rpow`: `1 + log x ≤ (1 + δ⁻¹) * x ^ δ` for `1 ≤ x` and `0 < δ`.
-/

public section

namespace Real

/-- For `1 ≤ x` and `0 < δ`, `1 + log x` is bounded above by `(1 + δ⁻¹) * x ^ δ`. -/
theorem one_add_log_le_mul_rpow {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    1 + log x ≤ (1 + δ⁻¹) * x ^ δ := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : 1 ≤ x ^ δ := one_le_rpow hx hδ.le
  have hlog : log x ≤ δ⁻¹ * x ^ δ := by
    simpa [div_eq_inv_mul] using log_le_rpow_div hx0 hδ
  linarith

end Real
