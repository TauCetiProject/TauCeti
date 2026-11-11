/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Integration

/-!
# Lp membership of independent products

A continuous operation bounded by a constant times the product of the norms preserves
`MemLp` for independent inputs with the same exponent. This applies to scalar multiplication
and multiplication, including the exponents zero and infinity.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory.IndepFun

variable {Ω E F G : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A continuous operation bounded by a constant times the product of the norms preserves
`MemLp` for independent inputs with the same exponent. -/
theorem memLp_op
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {p : ℝ≥0∞} {X : Ω → E} {Y : Ω → F} (hXY : IndepFun X Y P)
    (hX : MemLp X p P) (hY : MemLp Y p P) (B : E → F → G)
    (cB : Continuous B.uncurry) (C : ℝ≥0) (hB : ∀ x y, ‖B x y‖ₑ ≤ C * ‖x‖ₑ * ‖y‖ₑ) :
    MemLp (fun ω ↦ B (X ω) (Y ω)) p P := by
  have hm := cB.comp_aestronglyMeasurable₂ hX.aestronglyMeasurable hY.aestronglyMeasurable
  by_cases hp₀ : p = 0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.2 hm
  by_cases hp_top : p = ∞
  · subst p
    rw [memLp_iff, eLpNorm_exponent_top hm]
    have hXtop : eLpNormEssSup X P < ∞ := by
      simpa only [eLpNorm_exponent_top hX.aestronglyMeasurable] using hX.eLpNorm_lt_top
    have hYtop : eLpNormEssSup Y P < ∞ := by
      simpa only [eLpNorm_exponent_top hY.aestronglyMeasurable] using hY.eLpNorm_lt_top
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound (C :=
      (C : ℝ≥0∞) * eLpNormEssSup X P * eLpNormEssSup Y P) ?_)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by finiteness) hXtop) hYtop)
    filter_upwards [enorm_ae_le_eLpNormEssSup X P, enorm_ae_le_eLpNormEssSup Y P] with ω hωX hωY
    exact (hB _ _).trans (mul_le_mul' (mul_le_mul' le_rfl hωX) hωY)
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp_top hm).2
  calc
    _ ≤ (C : ℝ≥0∞) ^ p.toReal * ∫⁻ ω, ‖X ω‖ₑ ^ p.toReal * ‖Y ω‖ₑ ^ p.toReal ∂P := by
      rw [← lintegral_const_mul'' _
        ((hX.aestronglyMeasurable.enorm.pow_const p.toReal).fun_mul
          (hY.aestronglyMeasurable.enorm.pow_const p.toReal))]
      apply lintegral_mono
      intro ω
      calc
        _ ≤ ((C : ℝ≥0∞) * ‖X ω‖ₑ * ‖Y ω‖ₑ) ^ p.toReal :=
          ENNReal.rpow_le_rpow (hB _ _) ENNReal.toReal_nonneg
        _ = _ := by simp only [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, mul_assoc]
    _ = (C : ℝ≥0∞) ^ p.toReal *
        ((∫⁻ ω, ‖X ω‖ₑ ^ p.toReal ∂P) * ∫⁻ ω, ‖Y ω‖ₑ ^ p.toReal ∂P) := by
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        (hX.aestronglyMeasurable.enorm.pow_const p.toReal)
        (hY.aestronglyMeasurable.enorm.pow_const p.toReal)
        (hXY.comp (measurable_enorm.pow_const p.toReal) (measurable_enorm.pow_const p.toReal))]
    _ < ∞ := ENNReal.mul_lt_top (by finiteness)
      (ENNReal.mul_lt_top
        (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hp_top hX.eLpNorm_lt_top)
        (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hp_top hY.eLpNorm_lt_top))

/-- Scalar multiplication of independent `MemLp` random variables preserves their exponent. -/
theorem memLp_smul
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SMul E F] [ContinuousSMul E F] [ENormSMulClass E F]
    {p : ℝ≥0∞} {X : Ω → E} {Y : Ω → F} (hXY : IndepFun X Y P)
    (hX : MemLp X p P) (hY : MemLp Y p P) :
    MemLp (fun ω ↦ X ω • Y ω) p P :=
  hXY.memLp_op hX hY (· • ·) (by fun_prop) 1 (by simp [enorm_smul])

/-- Multiplication of independent `MemLp` random variables preserves their exponent. -/
theorem memLp_mul
    [TopologicalSpace E] [ContinuousENorm E] [Mul E] [ContinuousMul E] [ENormSMulClass E E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {p : ℝ≥0∞} {X Y : Ω → E} (hXY : IndepFun X Y P)
    (hX : MemLp X p P) (hY : MemLp Y p P) : MemLp (X * Y) p P :=
  hXY.memLp_smul hX hY

end ProbabilityTheory.IndepFun
