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
space, any nonnegative threshold `c < ‖A‖` below its essential-supremum operator norm is witnessed
at a single input vector `u : E` on a measurable set `t` with `0 < μ t < ∞`
(`MeasureTheory.Lp.exists_measurableSet_mul_norm_lt_norm_apply_measure_lt_top`). Testing on
`indicatorConstLp p ht _ u` then proves exact operator-norm equality
`‖operatorMultiplication p A‖ = ‖A‖` on `Lp E p μ` without any separability assumption on `E`,
since strong measurability of `A` makes its range separable in operator norm.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 E F : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a σ-finite measure space, every nonnegative `c < ‖A‖` is witnessed by a single vector
`u : E` and a measurable set `t` with `0 < μ t < ∞` on which `c * ‖u‖ < ‖A x u‖`. -/
theorem exists_measurableSet_mul_norm_lt_norm_apply_measure_lt_top [SigmaFinite μ]
    (A : Lp (E →L[𝕜] F) ∞ μ) {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt : c < ‖A‖) :
    ∃ (u : E) (t : Set α), MeasurableSet t ∧ (∀ x ∈ t, c * ‖u‖ < ‖A x u‖) ∧
      0 < μ t ∧ μ t < ∞ := by
  obtain ⟨C, hC_count, hC_sub⟩ := (Lp.stronglyMeasurable A).isSeparable_range
  set δ := (‖A‖ - c) / 3 with hδ_def
  have hδ : 0 < δ := by linarith [hδ_def]
  set S : Set (E →L[𝕜] F) := {B ∈ C | c + δ < ‖B‖}
  have : Countable S := (hC_count.mono (Set.sep_subset _ _)).to_subtype
  choose u hu using fun B : S ↦ show ∃ u : E, (c + δ) * ‖u‖ < ‖(B : E →L[𝕜] F) u‖ by
    by_contra! h; exact (not_le_of_gt B.2.2) ((B : E →L[𝕜] F).opNorm_le_bound (by linarith) h)
  have hcover : {x | c + 2 * δ < ‖A x‖} ⊆ ⋃ B : S, {x | c * ‖u B‖ < ‖A x (u B)‖} := fun x hx ↦ by
    obtain ⟨B, hBC, hdist⟩ := Metric.mem_closure_iff.mp (hC_sub ⟨x, rfl⟩) δ hδ
    rw [dist_comm, _root_.dist_eq_norm] at hdist
    have hBS : B ∈ S := ⟨hBC, by
      have := norm_sub_le B (B - A x); rw [sub_sub_cancel] at this; linarith [Set.mem_ofPred.mp hx]⟩
    have htri : ‖B (u ⟨B, hBS⟩)‖ ≤ ‖(B - A x) (u ⟨B, hBS⟩)‖ + ‖A x (u ⟨B, hBS⟩)‖ := by
      simpa only [sub_apply, sub_add_cancel] using
        norm_add_le ((B - A x) (u ⟨B, hBS⟩)) (A x (u ⟨B, hBS⟩))
    have hle := ((B - A x).le_opNorm (u ⟨B, hBS⟩)).trans
      (mul_le_mul_of_nonneg_right hdist.le (norm_nonneg _))
    have huB : (c + δ) * ‖u ⟨B, hBS⟩‖ < ‖B (u ⟨B, hBS⟩)‖ := hu ⟨B, hBS⟩
    exact Set.mem_iUnion.mpr ⟨⟨B, hBS⟩, Set.mem_ofPred.mpr (by nlinarith)⟩
  have hμ_union : μ (⋃ B : S, {x | c * ‖u B‖ < ‖A x (u B)‖}) ≠ 0 :=
    mt (measure_mono_null hcover) (Lp.measure_lt_norm_ne_zero (by linarith) (by linarith [hδ_def]))
  obtain ⟨B, hμs⟩ : ∃ B : S, μ {x | c * ‖u B‖ < ‖A x (u B)‖} ≠ 0 := by
    by_contra! hzero; exact hμ_union (measure_iUnion_null hzero)
  have hs : MeasurableSet {x | c * ‖u B‖ < ‖A x (u B)‖} := measurableSet_lt measurable_const
    (((ContinuousLinearMap.apply 𝕜 F (u B)).continuous.norm.comp_stronglyMeasurable
      (Lp.stronglyMeasurable A)).measurable)
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  exact ⟨u B, t, ht, hts, hμt_pos, hμt_top⟩

end MeasureTheory.Lp
