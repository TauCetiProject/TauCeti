/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.Count

/-!
# Hölder inequalities for finite `Lᵖ` spaces

Using the bridge `TauCeti.ofReal_norm_toLp_eq_eLpNorm_count` between finite `Lᵖ` norms and
`MeasureTheory.eLpNorm` for the counting measure, this file deduces the log-convex interpolation
Hölder inequality (`TauCeti.norm_toLp_rpow_mul_rpow_le`) from
`MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow_of_ae_le`.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Log-convex Hölder inequality for finite `Lᵖ` norms under the complex interpolation relation
`q⁻¹ = (1 - θ) / q₀ + θ / q₁` with `0 ≤ θ ≤ 1` and nonzero exponents `q₀, q₁`. -/
theorem norm_toLp_rpow_mul_rpow_le {q₀ q₁ q : ℝ≥0∞} (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2
  have hq_ne : q ≠ 0 := fun h ↦
    (hq.symm ▸ ENNReal.add_ne_top.2 ⟨by simp [ENNReal.mul_ne_top, hq₀],
      by simp [ENNReal.mul_ne_top, hq₁]⟩) (by simp [h])
  let _ : MeasurableSpace ι := ⊤; have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have h : ENNReal.ofReal ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ENNReal.ofReal ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ENNReal.ofReal ‖WithLp.toLp q₁ b‖ ^ θ := by
    rw [ofReal_norm_toLp_eq_eLpNorm_count hq_ne, ofReal_norm_toLp_eq_eLpNorm_count hq₀,
      ofReal_norm_toLp_eq_eLpNorm_count hq₁]
    refine MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow_of_ae_le hθ hq
      Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable
      Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun i ↦ ?_)
    simp [Real.eNorm_eq_ofReal_abs, abs_of_nonneg, ha i, hb i, h1θ, hθ.1,
      ENNReal.ofReal_rpow_of_nonneg, Real.rpow_nonneg]
  simpa [ENNReal.ofReal_rpow_of_nonneg (PiLp.norm_nonneg' _) h1θ,
    ENNReal.ofReal_rpow_of_nonneg (PiLp.norm_nonneg' _) hθ.1,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (PiLp.norm_nonneg' _) _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg (PiLp.norm_nonneg' _) _)
      (Real.rpow_nonneg (PiLp.norm_nonneg' _) _))] using h

end TauCeti
