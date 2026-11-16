/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Truncated second moments

For a real square-integrable function `X` and a level `ε`, the truncated square
`X ^ 2 𝟙{ε ≤ |X|}` is integrable (`MeasureTheory.MemLp.integrable_indicator_sq`), and on a
probability space the second moment splits as `E[X²] ≤ ε² + E[X²; ε ≤ |X|]`
(`MeasureTheory.MemLp.integral_sq_le_sq_add_integral_indicator`). The truncated second moment is
the quantity in the Lindeberg condition of the central limit theorem, and the split is how that
condition controls each individual variance. Only almost-everywhere measurability is used, through
`Integrable.indicator₀`.

For functions in `Lᵖ`, with finite positive `p` and values in a seminormed group, cutting off
values above increasing real norm levels makes the integral of the `p`-th power of the error
norm tend to zero. This supplies bounded approximations without requiring the underlying measure
to be finite.
-/

public section

open Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- The truncated square `X ^ 2 𝟙{ε ≤ |X|}` of a square-integrable function is integrable. -/
theorem MemLp.integrable_indicator_sq (hX : MemLp X 2 P) (ε : ℝ) :
    Integrable ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) P :=
  hX.integrable_sq.indicator₀
    (nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hX.aestronglyMeasurable.aemeasurable))

/-- Splitting the second moment at level `ε`: `E[X²] ≤ ε² + E[X²; ε ≤ |X|]`. -/
theorem MemLp.integral_sq_le_sq_add_integral_indicator [IsProbabilityMeasure P]
    (hX : MemLp X 2 P) (ε : ℝ) :
    ∫ ω, X ω ^ 2 ∂P ≤ ε ^ 2 + ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
  have h := hX.integrable_indicator_sq ε
  calc ∫ ω, X ω ^ 2 ∂P
      ≤ ∫ ω, (ε ^ 2 + ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω) ∂P := by
        refine integral_mono hX.integrable_sq ((integrable_const _).add h) fun ω ↦ ?_
        by_cases hω : ε ≤ |X ω|
        · rw [indicator_of_mem (s := {ω | ε ≤ |X ω|}) hω]
          linarith [sq_nonneg ε]
        · rw [indicator_of_notMem (s := {ω | ε ≤ |X ω|}) hω, add_zero,
            ← sq_abs (X ω)]
          have := abs_nonneg (X ω)
          nlinarith [not_le.mp hω]
    _ = ε ^ 2 + ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
        rw [integral_add (integrable_const _) h]
        simp

/-- Cutting off an `Lᵖ` function above increasing real norm levels gives errors whose
`p`-th norm-power integrals tend to zero, for finite positive `p`. No finiteness assumption
on the measure is needed. -/
theorem MemLp.tendsto_lintegral_eNorm_ite_sub_rpow
    {E : Type*} [SeminormedAddCommGroup E] {p : ℝ≥0∞} {f : Ω → E}
    (hf : MemLp f p P) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Filter.Tendsto (fun R : ℝ ↦ ∫⁻ x,
      ‖(if ‖f x‖ ≤ R then f x else 0) - f x‖ₑ ^ p.toReal ∂P) Filter.atTop (nhds 0) := by
  have hp_pos := ENNReal.toReal_pos hp0 hp
  have hmeas (R : ℝ) : AEStronglyMeasurable
      (fun x ↦ (if ‖f x‖ ≤ R then f x else 0) - f x) P := by
    simpa only [Pi.sub_def, Set.indicator_apply, mem_ofPred_eq] using
      (hf.aestronglyMeasurable.indicator₀
        (nullMeasurableSet_le hf.aestronglyMeasurable.norm.aemeasurable aemeasurable_const)).sub
          hf.aestronglyMeasurable
  have hdom (R : ℝ) (x : Ω) :
      ‖(if ‖f x‖ ≤ R then f x else 0) - f x‖ₑ ^ p.toReal ≤ ‖f x‖ₑ ^ p.toReal := by
    split_ifs <;> simp [ENNReal.zero_rpow_of_pos hp_pos]
  have hfinite : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂P < ∞ :=
    lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp hf.eLpNorm_lt_top
  have hlim (x : Ω) : Filter.Tendsto
      (fun R : ℝ ↦ ‖(if ‖f x‖ ≤ R then f x else 0) - f x‖ₑ ^ p.toReal)
        Filter.atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop ‖f x‖] with R hR
    simp [hR, ENNReal.zero_rpow_of_pos hp_pos]
  simpa using tendsto_lintegral_filter_of_dominated_convergence' (fun x ↦ ‖f x‖ₑ ^ p.toReal)
    (Filter.Eventually.of_forall fun R ↦ (hmeas R).eNorm.pow_const p.toReal)
    (Filter.Eventually.of_forall fun R ↦ Filter.Eventually.of_forall (hdom R))
    hfinite.ne (Filter.Eventually.of_forall hlim)

end MeasureTheory
