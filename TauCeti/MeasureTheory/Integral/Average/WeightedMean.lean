/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity

/-!
# The weighted mean minimizes the weighted squared deviation

For an integrable weight `w ≥ 0`, the center `c = (∫ X w) / (∫ w)` minimizes the weighted squared
deviation `∫⁻ (c - X)² w`. This is the best-constant property of the average applied to the
weighted measure `μ.withDensity (ofReal ∘ w)`.

## Main results

* `TauCeti.lintegral_ofReal_sub_sq_mul_le`: for an integrable weight `w ≥ 0`, `(∫ X w) / (∫ w)`
  (the weighted mean if `X w` is integrable, else all deviations are `∞`) minimizes `∫⁻ (c - X)² w`.
-/

public section

namespace TauCeti

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X w : Ω → ℝ}

/-- **The weighted mean minimizes the weighted squared deviation.** For an integrable a.e.
nonnegative weight `w` and an `X` that is a.e. strongly measurable for the weighted measure
`μ.withDensity (ofReal ∘ w)`, the weighted squared deviation `∫⁻ ω, ofReal ((c - X ω)² w ω) ∂μ`,
which may be infinite, is smallest at `c = (∫ X w ∂μ) / (∫ w ∂μ)`, the weighted mean when `X w` is
integrable. No first moment is assumed: otherwise `X` is not square integrable for the weighted
measure, every center has infinite deviation, and Lean's totalized formula satisfies the inequality
too. When `w` has zero mass, it vanishes a.e. and every center has zero deviation.

The proof applies `TauCeti.setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq` to the
weighted measure `μ.withDensity (ofReal ∘ w)`. The statement is adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), file `CKSD/Inference/Families.lean`
(`lintegral_ofReal_sq_sub_mul_le`, for `X = id` on `ℝ`). -/
theorem lintegral_ofReal_sub_sq_mul_le
    (hX : AEStronglyMeasurable X (μ.withDensity fun ω ↦ ENNReal.ofReal (w ω)))
    (hw0 : 0 ≤ᵐ[μ] w) (hwi : Integrable w μ) (c : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (((∫ ω, X ω * w ω ∂μ) / (∫ ω, w ω ∂μ) - X ω) ^ 2 * w ω) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((c - X ω) ^ 2 * w ω) ∂μ := by
  set ν := μ.withDensity fun ω ↦ ENNReal.ofReal (w ω)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hwi.2
  have hXc (d : ℝ) : AEStronglyMeasurable (fun ω ↦ X ω - d) ν := hX.sub aestronglyMeasurable_const
  -- The weighted lower integrals are lower integrals against `ν`.
  have hlin (d : ℝ) : ∫⁻ ω, ENNReal.ofReal ((d - X ω) ^ 2 * w ω) ∂μ =
      ∫⁻ ω, ‖X ω - d‖ₑ ^ 2 ∂ν := by
    rw [lintegral_withDensity_eq_lintegral_mul₀' hwi.aemeasurable.ennreal_ofReal
      ((hXc d).aemeasurable.eNorm.pow_const 2)]
    refine lintegral_congr_ae ?_
    filter_upwards [hw0] with ω hω
    rw [Pi.mul_apply, Real.enorm_sq_eq_ofReal_sq, ← ENNReal.ofReal_mul hω, sub_sq_comm (X ω) d,
      mul_comm (w ω)]
  -- The weighted mean is the average of `X` under `ν`.
  have hmean : ⨍ ω, X ω ∂ν = (∫ ω, X ω * w ω ∂μ) / (∫ ω, w ω ∂μ) := by
    have hν : ν.real Set.univ = ∫ ω, w ω ∂μ := by
      simpa using TauCeti.MeasureTheory.measureReal_withDensity_ofReal (s := Set.univ)
        (ae_restrict_of_ae hw0) MeasurableSet.univ.nullMeasurableSet hwi.aemeasurable.restrict
    rw [average_eq, hν, TauCeti.MeasureTheory.integral_withDensity_ofReal hwi.aemeasurable hw0,
      smul_eq_mul, inv_mul_eq_div]
    simp_rw [smul_eq_mul, mul_comm (w _)]
  rw [hlin, hlin, ← hmean]
  rcases eq_top_or_lt_top (∫⁻ ω, ‖X ω - c‖ₑ ^ 2 ∂ν) with hfin | hfin
  · exact hfin ▸ le_top
  have hc := (hXc c).memLp_two_iff_lintegral_enorm_sq_lt_top.2 hfin
  have h2 : MemLp X 2 ν := by simpa [Pi.add_def] using hc.add (memLp_const c)
  have hm : MemLp (fun ω ↦ X ω - ⨍ ω, X ω ∂ν) 2 ν := h2.sub (memLp_const _)
  have key := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
    (measure_ne_top ν Set.univ) (h2.integrable one_le_two).integrableOn
    (hc.integrable_norm_pow two_ne_zero).integrableOn
  rw [Measure.restrict_univ] at key
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (hm.integrable_norm_pow two_ne_zero)
      (ae_of_all _ fun _ ↦ by positivity),
    ← ofReal_integral_eq_lintegral_ofReal (hc.integrable_norm_pow two_ne_zero)
      (ae_of_all _ fun _ ↦ by positivity)]
  exact ENNReal.ofReal_le_ofReal key

end TauCeti
