/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Norm localization for operator-valued `L∞` functions

For an essentially bounded operator-valued function `A : Lp (E →L[𝕜] F) ∞ μ` on a σ-finite measure
space whose domain fibre `E` has a second-countable topology, any nonnegative threshold `c < ‖A‖` is
witnessed simultaneously at a single vector `u : E` on a measurable set `t` of positive finite
measure (`MeasureTheory.Lp.exists_subset_measure_lt_norm_apply`): countable density in `E` upgrades
the positive-measure operator-norm level set of `MeasureTheory.Lp.measure_lt_norm_ne_zero` to a
fixed input vector, and σ-finiteness trims it to finite measure via
`MeasureTheory.Measure.exists_subset_measure_lt_top`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a σ-finite measure space with second-countable domain fibre `E`, every nonnegative level
`c < ‖A‖` strictly below the `L∞` operator norm of `A : Lp (E →L[𝕜] F) ∞ μ` is witnessed by a
single vector `u : E` and a measurable set `t` with `0 < μ t < ∞` on which `c * ‖u‖ < ‖A x u‖`. -/
theorem exists_subset_measure_lt_norm_apply [SigmaFinite μ] (A : Lp (E →L[𝕜] F) ∞ μ)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt : c < ‖A‖) :
    ∃ (u : E) (t : Set α), MeasurableSet t ∧ (∀ x ∈ t, c * ‖u‖ < ‖A x u‖) ∧
      0 < μ t ∧ μ t < ∞ := by
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense E
  have hsub : {x | c < ‖A x‖} ⊆ ⋃ u ∈ D, {x | c * ‖u‖ < ‖A x u‖} := fun x hx ↦ by
    have hnot : ¬ ∀ w : E, ‖A x w‖ ≤ c * ‖w‖ := fun h ↦
      (not_le_of_gt hx) ((A x).opNorm_le_bound hc_nonneg h)
    push Not at hnot; obtain ⟨w, hw⟩ := hnot
    obtain ⟨u, huU, huD⟩ := hD_dense.inter_open_nonempty {u : E | c * ‖u‖ < ‖A x u‖}
      (isOpen_lt (by fun_prop) (by fun_prop)) ⟨w, hw⟩
    exact Set.mem_biUnion huD huU
  have hμ_union : μ (⋃ u ∈ D, {x | c * ‖u‖ < ‖A x u‖}) ≠ 0 :=
    mt (measure_mono_null hsub) (Lp.measure_lt_norm_ne_zero hc_nonneg hc_lt)
  obtain ⟨u, _, hμs⟩ : ∃ u ∈ D, μ {x | c * ‖u‖ < ‖A x u‖} ≠ 0 := by
    by_contra! hzero; exact hμ_union ((measure_biUnion_null_iff hD_count).2 hzero)
  have hs : MeasurableSet {x | c * ‖u‖ < ‖A x u‖} := measurableSet_lt measurable_const
    (((ContinuousLinearMap.apply 𝕜 F u).continuous.norm.comp_stronglyMeasurable
      (Lp.stronglyMeasurable A)).measurable)
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  exact ⟨u, t, ht, hts, hμt_pos, hμt_top⟩

end MeasureTheory.Lp
