/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Local integral bound for a bounded operator applied to a cut-off function

Let `T` be a bounded linear operator on `Lᵖ(μ)` with `1 ≤ p`, and let `g ∈ Lᵖ` agree almost
everywhere with `f` cut off to a set `s`. By Hölder's inequality on `t` and on `s`,

`∫_t ‖T g‖ ≤ ‖T‖ ‖f‖_∞ (μ s)^{1/p} (μ t)^{1 - 1/p}`.

This is the estimate of the local part of a function in the Calderón–Zygmund decomposition at the
`L^∞` endpoint, where `s` is an enlarged ball and `t` the ball itself.

## Main declarations

* `ContinuousLinearMap.setLIntegral_enorm_apply_le_of_ae_eq_indicator`: the bound above.
* `ContinuousLinearMap.setLIntegral_enorm_apply_le_of_ae_eq_indicator_of_measure_le`: the bound
  `D^{1/p} ‖T‖ ‖f‖_∞ μ t` when `μ s ≤ D * μ t`.
-/

public section

namespace ContinuousLinearMap

open MeasureTheory Set
open scoped ENNReal

variable {X 𝕜 E F : Type*} [MeasurableSpace X] {μ : Measure X} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If `g ∈ Lᵖ`, `1 ≤ p`, agrees almost everywhere with a function `f` cut off to a measurable set
`s`, then the integral of `‖T g‖` over a set `t` is at most
`‖T‖ ‖f‖_∞ (μ s)^{1/p} (μ t)^{1 - 1/p}`, by Hölder's inequality and the `Lᵖ` bound for `T`. -/
theorem setLIntegral_enorm_apply_le_of_ae_eq_indicator (T : Lp E p μ →L[𝕜] Lp F p μ)
    {f g : Lp E p μ} {s : Set X} (hs : MeasurableSet s) (hg : g =ᵐ[μ] s.indicator f) (t : Set X) :
    ∫⁻ x in t, ‖T g x‖ₑ ∂μ ≤
      ‖T‖ₑ * (eLpNorm f ∞ μ * μ s ^ p.toReal⁻¹) * μ t ^ (1 - p.toReal⁻¹) := by
  have hp : 1 ≤ p := Fact.out
  calc ∫⁻ x in t, ‖T g x‖ₑ ∂μ
      = eLpNorm (T g) 1 (μ.restrict t) :=
        (eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _).restrict).symm
    _ ≤ eLpNorm (T g) p (μ.restrict t) * μ t ^ (1 - p.toReal⁻¹) := by
        refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := p) hp
          (Lp.aestronglyMeasurable _).restrict).trans_eq ?_
        rw [Measure.restrict_apply_univ]
        simp
    _ ≤ ‖T‖ₑ * (eLpNorm f ∞ μ * μ s ^ p.toReal⁻¹) * μ t ^ (1 - p.toReal⁻¹) := by
        gcongr
        refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
        rw [← Lp.enorm_def]
        refine T.le_opENorm_of_le ?_
        rw [Lp.enorm_def, eLpNorm_congr_ae hg,
          eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
        calc eLpNorm f p (μ.restrict s)
            ≤ eLpNorm f ∞ (μ.restrict s) *
                μ.restrict s univ ^ (1 / p.toReal - 1 / (∞ : ℝ≥0∞).toReal) :=
              eLpNorm_le_eLpNorm_mul_rpow_measure_univ le_top (Lp.aestronglyMeasurable f).restrict
          _ ≤ eLpNorm f ∞ μ * μ s ^ p.toReal⁻¹ := by
              rw [Measure.restrict_apply_univ]
              simp only [ENNReal.toReal_top, div_zero, sub_zero, one_div]
              gcongr
              exact Measure.restrict_le_self

/-- If, moreover, `μ s ≤ D * μ t` and `t` has finite positive measure, then the integral of `‖T g‖`
over `t` is at most `D^{1/p} ‖T‖ ‖f‖_∞ μ t`, since `(μ s)^{1/p} (μ t)^{1 - 1/p} ≤ D^{1/p} μ t`. -/
theorem setLIntegral_enorm_apply_le_of_ae_eq_indicator_of_measure_le
    (T : Lp E p μ →L[𝕜] Lp F p μ) {f g : Lp E p μ} {s t : Set X} {D : ℝ≥0∞}
    (hs : MeasurableSet s) (hg : g =ᵐ[μ] s.indicator f) (hD : μ s ≤ D * μ t) (h0 : μ t ≠ 0)
    (htop : μ t ≠ ∞) :
    ∫⁻ x in t, ‖T g x‖ₑ ∂μ ≤ D ^ p.toReal⁻¹ * ‖T‖ₑ * eLpNorm f ∞ μ * μ t := by
  have hp : 0 ≤ p.toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  have hsq : μ t ^ p.toReal⁻¹ * μ t ^ (1 - p.toReal⁻¹) = μ t := by
    rw [← ENNReal.rpow_add _ _ h0 htop, add_sub_cancel, ENNReal.rpow_one]
  calc ∫⁻ x in t, ‖T g x‖ₑ ∂μ
      ≤ ‖T‖ₑ * (eLpNorm f ∞ μ * μ s ^ p.toReal⁻¹) * μ t ^ (1 - p.toReal⁻¹) :=
        setLIntegral_enorm_apply_le_of_ae_eq_indicator T hs hg t
    _ ≤ ‖T‖ₑ * (eLpNorm f ∞ μ * (D * μ t) ^ p.toReal⁻¹) * μ t ^ (1 - p.toReal⁻¹) := by gcongr
    _ = D ^ p.toReal⁻¹ * ‖T‖ₑ * eLpNorm f ∞ μ *
          (μ t ^ p.toReal⁻¹ * μ t ^ (1 - p.toReal⁻¹)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
        ring
    _ = D ^ p.toReal⁻¹ * ‖T‖ₑ * eLpNorm f ∞ μ * μ t := by rw [hsq]

end ContinuousLinearMap
