/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.CantorCircle
public import TauCeti.MeasureTheory.Function.MetricDerivative.Basic

/-!
# The speed of a circle traversed along the Cantor function

Let `φ(t) = (t + C(t)) / 2` be `TauCeti.cantorReparam`, with `C` the Cantor–Lebesgue function. It
is not absolutely continuous (`TauCeti.not_absolutelyContinuousOnInterval_cantorReparam`):
`φ' = 1/2` at almost every point (`TauCeti.ae_hasDerivAt_cantorReparam`), so `∫₀¹ φ' = 1/2`
(`TauCeti.integral_deriv_cantorReparam`), while `φ(1) − φ(0) = 1`.

The curve `γ(t) = exp(2πi φ(t))` (`TauCeti.cantorCircle`) is closed, injective on `[0, 1)` and has
length `2π` (`TauCeti.eVariationOn_cantorCircle`). Almost everywhere `‖γ'(t)‖ = 2π φ'(t) = π`
(`TauCeti.ae_norm_deriv_cantorCircle`), so `∫₀¹ ‖γ'‖ = π ≠ 2π`
(`integral_norm_deriv_cantorCircle`): the length formula `length = ∫ ‖γ'‖` needs absolute
continuity. For this curve of bounded variation the metric derivative still equals `‖γ'‖`
almost everywhere: it is `π` at almost every time of `[0, 1]` (`ae_metricDerivative_cantorCircle`).
-/

@[expose] public section

open Real MeasureTheory Set

namespace TauCeti.Examples.CantorCircle

/-- **The length formula fails.** `∫₀¹ ‖γ'‖ = π`, half the length `2π` of `γ`
(`TauCeti.eVariationOn_cantorCircle`). -/
theorem integral_norm_deriv_cantorCircle : ∫ t in (0 : ℝ)..1, ‖deriv cantorCircle t‖ = π := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ π)
    (ae_norm_deriv_cantorCircle.mono fun _ ht _ ↦ ht)]
  simp

/-- **The metric speed is `π`.** The metric derivative of `γ` equals `‖γ'‖ₑ = π` at almost every
time of `[0, 1]`. -/
theorem ae_metricDerivative_cantorCircle :
    ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → metricDerivative cantorCircle t = ENNReal.ofReal π := by
  have hγ : BoundedVariationOn cantorCircle (uIcc 0 1) := by
    simpa [uIcc_of_le zero_le_one] using boundedVariationOn_cantorCircle
  filter_upwards [hγ.ae_metricDerivative_eq_enorm_deriv, ae_norm_deriv_cantorCircle]
    with t ht hnorm hmem
  rw [ht (by simpa [uIcc_of_le zero_le_one] using hmem), ← ofReal_norm, hnorm]

end TauCeti.Examples.CantorCircle
