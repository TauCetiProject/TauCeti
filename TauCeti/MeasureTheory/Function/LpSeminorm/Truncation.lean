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

For square-integrable functions with values in a seminormed group, cutting off values above
increasing norm levels makes the square energy of the error tend to zero. This supplies bounded
approximations without requiring the underlying measure to be finite.
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

/-- Cutting off a square-integrable function above increasing norm levels gives errors whose
square energies tend to zero. No finiteness assumption on the measure is needed. -/
theorem MemLp.tendsto_lintegral_enorm_sub_truncation
    {E : Type*} [SeminormedAddCommGroup E] {f : Ω → E} (hf : MemLp f 2 P) :
    Filter.Tendsto (fun m : ℕ ↦ ∫⁻ x,
      ‖(if ‖f x‖ ≤ m then f x else 0) - f x‖ₑ ^ 2 ∂P) Filter.atTop (nhds 0) := by
  classical
  have hmeas (m : ℕ) : AEStronglyMeasurable
      (fun x ↦ (if ‖f x‖ ≤ m then f x else 0) - f x) P :=
    (hf.aestronglyMeasurable.indicator₀
      (nullMeasurableSet_le hf.aestronglyMeasurable.norm.aemeasurable aemeasurable_const)).sub
        hf.aestronglyMeasurable
  have hdom (m : ℕ) (x : Ω) :
      ‖(if ‖f x‖ ≤ m then f x else 0) - f x‖ₑ ^ 2 ≤ ‖f x‖ₑ ^ 2 := by
    split_ifs <;> simp
  have hfinite : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂P < ∞ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num)
        hf.eLpNorm_lt_top
  have hlim (x : Ω) : Filter.Tendsto
      (fun m : ℕ ↦ ‖(if ‖f x‖ ≤ m then f x else 0) - f x‖ₑ ^ 2) Filter.atTop (nhds 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖f x‖
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    have hm' : ‖f x‖ ≤ (m : ℝ) := hN.trans (Nat.cast_le.mpr hm)
    simp [hm']
  simpa using tendsto_lintegral_of_dominated_convergence' (fun x ↦ ‖f x‖ₑ ^ 2)
    (fun m ↦ (hmeas m).eNorm.pow_const 2) (fun m ↦ Filter.Eventually.of_forall (hdom m))
    hfinite.ne (Filter.Eventually.of_forall hlim)

end MeasureTheory
