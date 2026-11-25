/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.CantorCircle
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# The speed of a circle traversed along the Cantor function

Let `φ(t) = (t + C(t)) / 2` be `TauCeti.cantorReparam`, with `C` the Cantor–Lebesgue function. It
is not absolutely continuous (`TauCeti.not_absolutelyContinuousOnInterval_cantorReparam`):
`φ' = 1/2` at almost every point (`ae_hasDerivAt_cantorReparam`), so `∫₀¹ φ' = 1/2`
(`integral_deriv_cantorReparam`), while `φ(1) − φ(0) = 1`.

The curve `γ(t) = exp(2πi φ(t))` (`TauCeti.cantorCircle`) is closed, injective on `[0, 1)` and has
length `2π` (`TauCeti.eVariationOn_cantorCircle`). Almost everywhere `‖γ'(t)‖ = 2π φ'(t) = π`
(`ae_norm_deriv_cantorCircle`), so `∫₀¹ ‖γ'‖ = π ≠ 2π` (`integral_norm_deriv_cantorCircle`): the
length formula `length = ∫ ‖γ'‖` needs absolute continuity.

This is the first Check of §1.1 of `TauCetiRoadmap/GeometricMeasureTheory/README.md`.
-/

@[expose] public section

noncomputable section

open Real Set MeasureTheory

namespace TauCeti.Examples.CantorCircle

/-- Off the Cantor set, `φ' = 1/2`. -/
theorem hasDerivAt_cantorReparam_of_notMem {t : ℝ} (ht : t ∉ cantorSet) :
    HasDerivAt cantorReparam (1 / 2) t := by
  convert ((hasDerivAt_id t).add (hasDerivAt_cantorFunction_of_notMem ht)).div_const 2 using 1
  · exact funext cantorReparam_apply
  · norm_num

/-- `φ' = 1/2` at almost every point. -/
theorem ae_hasDerivAt_cantorReparam : ∀ᵐ t, HasDerivAt cantorReparam (1 / 2) t :=
  (measure_eq_zero_iff_ae_notMem.mp volume_cantorSet).mono
    fun _ => hasDerivAt_cantorReparam_of_notMem

/-- `∫₀¹ φ' = 1/2`, while `φ(1) − φ(0) = 1`: `φ` is not absolutely continuous
(`TauCeti.not_absolutelyContinuousOnInterval_cantorReparam`). -/
theorem integral_deriv_cantorReparam : ∫ t in (0 : ℝ)..1, deriv cantorReparam t = 1 / 2 := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 / 2 : ℝ))
    (ae_hasDerivAt_cantorReparam.mono fun t ht _ => ht.deriv)]
  simp

/-- Off the Cantor set, `γ' = π i γ`. -/
theorem hasDerivAt_cantorCircle_of_notMem {t : ℝ} (ht : t ∉ cantorSet) :
    HasDerivAt cantorCircle ((2 * π * (1 / 2) : ℝ) • (circleMap 0 1 (2 * π * cantorReparam t) *
      Complex.I)) t := by
  rw [funext cantorCircle_apply]
  exact (hasDerivAt_circleMap 0 1 _).scomp t
    ((hasDerivAt_cantorReparam_of_notMem ht).const_mul (2 * π))

/-- `‖γ'(t)‖ = 2π φ'(t) = π` at almost every `t`. -/
theorem ae_norm_deriv_cantorCircle : ∀ᵐ t, ‖deriv cantorCircle t‖ = π :=
  (measure_eq_zero_iff_ae_notMem.mp volume_cantorSet).mono fun t ht => by
    rw [(hasDerivAt_cantorCircle_of_notMem ht).deriv, norm_smul, norm_mul (circleMap 0 1 _),
      norm_circleMap_zero,
      Complex.norm_I, abs_one, mul_one, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring

/-- **The length formula fails.** `∫₀¹ ‖γ'‖ = π`, half the length `2π` of `γ`
(`TauCeti.eVariationOn_cantorCircle`). -/
theorem integral_norm_deriv_cantorCircle : ∫ t in (0 : ℝ)..1, ‖deriv cantorCircle t‖ = π := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => π)
    (ae_norm_deriv_cantorCircle.mono fun t ht _ => ht)]
  simp

end TauCeti.Examples.CantorCircle
