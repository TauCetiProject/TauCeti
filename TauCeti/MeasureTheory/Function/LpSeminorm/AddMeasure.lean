/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Monotonicity and subadditivity of `eLpNorm` in the measure

For `1 ≤ p`, the `Lᵖ` seminorm is subadditive in the measure:
`eLpNorm f p (μ + ν) ≤ eLpNorm f p μ + eLpNorm f p ν`
(`MeasureTheory.eLpNorm_add_measure_le`). For `p < ∞` this is the inequality
`(a + b) ^ (1 / p) ≤ a ^ (1 / p) + b ^ (1 / p)`, and for `p = ∞` the essential supremum for
`μ + ν` is the maximum of the two essential suprema. Mathlib has the equality for `p = 1`
(`MeasureTheory.eLpNorm_one_add_measure`); for `p < 1` the inequality fails.

Restricting to a finite union of sets gives the form used to pass from local estimates to an
estimate on a set covered by finitely many pieces
(`MeasureTheory.eLpNorm_restrict_biUnion_finset_le`):
`eLpNorm f p (μ.restrict (⋃ i ∈ t, s i)) ≤ ∑ i ∈ t, eLpNorm f p (μ.restrict (s i))`.
No measurability of the sets is needed.

For the real-valued norm `lpNorm`, monotonicity in the measure needs `f ∈ Lᵖ(μ)`, since
`lpNorm` is `0` off `Lᵖ` (`MeasureTheory.lpNorm_mono_measure`).

## Main declarations

* `MeasureTheory.lpNorm_mono_measure`: monotonicity of `lpNorm` in the measure.
* `MeasureTheory.eLpNorm_add_measure_le`: subadditivity in the measure.
* `MeasureTheory.eLpNorm_restrict_biUnion_finset_le`: subadditivity over a finite union.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α ε : Type*} {m : MeasurableSpace α} [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace.PseudoMetrizableSpace ε] {p : ℝ≥0∞} {μ ν : Measure α}

/-- **Monotonicity of `lpNorm` in the measure.** If `f ∈ Lᵖ(μ)` and `ν ≤ μ`, then
`lpNorm f p ν ≤ lpNorm f p μ`. -/
theorem lpNorm_mono_measure {E : Type*} [NormedAddCommGroup E] {f : α → E} (hf : MemLp f p μ)
    (hνμ : ν ≤ μ) :
    lpNorm f p ν ≤ lpNorm f p μ :=
  ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hνμ)

/-- **Subadditivity of `eLpNorm` in the measure.** For `1 ≤ p`,
`eLpNorm f p (μ + ν) ≤ eLpNorm f p μ + eLpNorm f p ν`. -/
theorem eLpNorm_add_measure_le (f : α → ε) (hp : 1 ≤ p) :
    eLpNorm f p (μ + ν) ≤ eLpNorm f p μ + eLpNorm f p ν := by
  by_cases hadd : AEStronglyMeasurable f (μ + ν)
  · have hfμ : AEStronglyMeasurable f μ := hadd.mono_measure (Measure.le_add_right le_rfl)
    have hfν : AEStronglyMeasurable f ν := hadd.mono_measure (Measure.le_add_left le_rfl)
    by_cases hp_top : p = ∞
    · subst hp_top
      rw [eLpNorm_exponent_top hadd, eLpNorm_exponent_top hfμ, eLpNorm_exponent_top hfν,
        eLpNormEssSup_add_measure]
      exact max_le_add_of_nonneg (by simp) (by simp)
    · have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
      have hp1 : 1 ≤ p.toReal := by
        simpa using ENNReal.toReal_mono hp_top hp
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hadd,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hfμ,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hfν, lintegral_add_measure]
      exact ENNReal.rpow_add_le_add_rpow _ _ (by positivity)
        (div_le_one_of_le₀ hp1 (by positivity))
  · by_cases hfμ : AEStronglyMeasurable f μ
    · have hfν : ¬ AEStronglyMeasurable f ν := fun hfν => hadd (hfμ.add_measure hfν)
      simp [eLpNorm_of_not_aestronglyMeasurable, hadd, hfν]
    · simp [eLpNorm_of_not_aestronglyMeasurable, hadd, hfμ]

/-- **Subadditivity of `eLpNorm` over a finite union.** For `1 ≤ p`, the `Lᵖ` seminorm of `f`
on a finite union of sets is at most the sum of its `Lᵖ` seminorms on the pieces. The sets need
not be measurable or disjoint. -/
theorem eLpNorm_restrict_biUnion_finset_le {ι : Type*} (f : α → ε) (hp : 1 ≤ p) (t : Finset ι)
    (s : ι → Set α) :
    eLpNorm f p (μ.restrict (⋃ i ∈ t, s i)) ≤ ∑ i ∈ t, eLpNorm f p (μ.restrict (s i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    calc eLpNorm f p (μ.restrict (s a ∪ ⋃ i ∈ t, s i))
        ≤ eLpNorm f p (μ.restrict (s a) + μ.restrict (⋃ i ∈ t, s i)) :=
          eLpNorm_mono_measure _ (Measure.restrict_union_le _ _)
      _ ≤ eLpNorm f p (μ.restrict (s a)) + eLpNorm f p (μ.restrict (⋃ i ∈ t, s i)) :=
          eLpNorm_add_measure_le f hp
      _ ≤ _ := by gcongr

end MeasureTheory
