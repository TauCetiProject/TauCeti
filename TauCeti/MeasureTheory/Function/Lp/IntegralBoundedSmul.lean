/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals of `Lᵖ` functions against bounded multipliers on finite-measure sets

If `h ∈ Lᵖ`, `1 ≤ p`, vanishes a.e. off a set `W` of finite measure and `k` is a scalar
multiplier a.e. bounded by `B` on `W`, then `k • h` is integrable and, by Hölder's
inequality on `W`,

`‖∫ k • h‖ ≤ B μ(W) ^ (1 - 1/p) ‖h‖_p`

(`TauCeti.integrable_smul_and_norm_integral_smul_le`). This is the estimate that makes
`h ↦ ∫ k • h` continuous on `Lᵖ` functions supported in `W`, used to pass to the limit in kernel
integrals `∫ K(x - y) h(y) dy` for `x` away from the support of `h`.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- If `k` is a.e. bounded by `B` on a set `W` of finite measure, and `h ∈ Lᵖ`, `1 ≤ p`,
vanishes a.e. off `W`, then `k • h` is integrable and, by Hölder's inequality on `W`,
`‖∫ k • h‖ ≤ B μ(W) ^ (1 - 1/p) ‖h‖_p`. -/
theorem integrable_smul_and_norm_integral_smul_le {k : α → ℝ} {W : Set α} (hμW : μ W ≠ ∞)
    {B : ℝ} (hB : 0 ≤ B) (hk : AEStronglyMeasurable k (μ.restrict W))
    (hkB : ∀ᵐ y ∂μ.restrict W, ‖k y‖ ≤ B) {p : ℝ≥0∞} (hp : 1 ≤ p) {h : α → F}
    (hh : MemLp h p μ) (h0 : ∀ᵐ y ∂μ, y ∉ W → h y = 0) :
    Integrable (fun y => k y • h y) μ ∧
      ‖∫ y, k y • h y ∂μ‖ ≤ B * (μ W ^ (1 - 1 / p.toReal) * eLpNorm h p μ).toReal := by
  have : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.2 hμW
  have hexp : 0 ≤ 1 - 1 / p.toReal := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    · have h1p : (1 : ℝ) ≤ p.toReal := by
        simpa using ENNReal.toReal_mono hp_top hp
      exact sub_nonneg.2 (div_le_one_of_le₀ h1p (by positivity))
  have hhW : IntegrableOn h W μ := (hh.restrict W).integrable hp
  have hbound : ∀ᵐ y ∂μ.restrict W, ‖k y • h y‖ ≤ B * ‖h y‖ := hkB.mono fun y hy => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
  have hint : IntegrableOn (fun y => k y • h y) W μ :=
    (hhW.norm.const_mul B).mono' (hk.smul (hh.restrict W).aestronglyMeasurable) hbound
  have hkh0 : ∀ᵐ y ∂μ, y ∉ W → k y • h y = 0 := h0.mono fun y hy hyW => by simp [hy hyW]
  refine ⟨hint.integrable_of_ae_notMem_eq_zero hkh0, ?_⟩
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hkh0]
  refine (norm_integral_le_of_norm_le (hhW.norm.const_mul B) hbound).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ hB
  rw [integral_norm_eq_lintegral_enorm (hh.restrict W).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm (hh.restrict W).aestronglyMeasurable]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hexp hμW)
    hh.eLpNorm_ne_top) ?_
  calc eLpNorm h 1 (μ.restrict W)
      ≤ eLpNorm h p (μ.restrict W) * μ.restrict W univ ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hh.restrict W).aestronglyMeasurable
    _ ≤ eLpNorm h p μ * μ W ^ (1 - 1 / p.toReal) := by
        rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one]
        gcongr
        exact Measure.restrict_le_self
    _ = _ := mul_comm _ _

end TauCeti
