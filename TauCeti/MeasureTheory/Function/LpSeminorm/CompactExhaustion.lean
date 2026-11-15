/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# `Lᵖ` seminorms on an open set through compact subsets

Let `U` be an open subset of a proper metric space and `1 ≤ p < ∞`. The `Lᵖ` seminorm of a function
on `U` is controlled by its seminorms on the compact subsets of `U`:

* if `‖f‖_{Lᵖ(K)} ≤ C` for every compact `K ⊆ U`, then `‖f‖_{Lᵖ(U)} ≤ C`
  (`MeasureTheory.eLpNorm_restrict_le_of_forall_isCompact`);
* if `‖f‖_{Lᵖ(U)} < ∞`, then for every `ε > 0` there is a compact `K ⊆ U` with
  `‖f‖_{Lᵖ(U \ K)} ≤ ε` (`MeasureTheory.exists_isCompact_eLpNorm_restrict_sdiff_le`);
* for a measurable `K`, `‖f‖_{Lᵖ(U)} ≤ ‖f‖_{Lᵖ(K)} + ‖f‖_{Lᵖ(U \ K)}`
  (`MeasureTheory.eLpNorm_restrict_le_add_restrict_sdiff`).

Both follow from an increasing exhaustion of `U` by compact sets: the integral of `‖f‖ᵖ` over `U`
is the supremum of its integrals over the exhausting sets, and the integrals over their complements
in `U` tend to zero by dominated convergence. Together they carry an estimate proved on compact sets
to all of `U`: a bound passes to `U` directly, and a convergence statement on compact sets passes to
`U` once the tail of a fixed function has been cut off.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal

namespace MeasureTheory

variable {X F : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup F] {μ : Measure X} {U : Set X} {p : ℝ≥0∞}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- An open subset of a proper metric space is the union of an increasing sequence of compact
subsets. -/
private theorem exists_monotone_isCompact_iUnion_eq (hU : IsOpen U) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ U) ∧ Monotone K ∧ ⋃ n, K n = U := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ => ∅, fun _ => isCompact_empty, fun _ => empty_subset _, fun _ _ _ => le_rfl,
      by simp [eq_empty_of_isEmpty U]⟩
  obtain ⟨C, hCc, hCU, hCun, hCm⟩ := hU.exists_iUnion_isClosed
  refine ⟨fun n => C n ∩ closedBall x₀ n, fun n => (isCompact_closedBall x₀ _).inter_left (hCc n),
    fun n => inter_subset_left.trans (hCU n), fun m n hmn => inter_subset_inter (hCm hmn)
      (closedBall_subset_closedBall (by exact_mod_cast hmn)), ?_⟩
  refine Subset.antisymm (iUnion_subset fun n => inter_subset_left.trans (hCU n)) fun x hx => ?_
  rw [← hCun, mem_iUnion] at hx
  obtain ⟨m, hm⟩ := hx
  obtain ⟨k, hk⟩ := exists_nat_ge (dist x x₀)
  exact mem_iUnion.2 ⟨max m k, hCm (le_max_left m k) hm,
    mem_closedBall.2 (hk.trans (by exact_mod_cast le_max_right m k))⟩

omit [OpensMeasurableSpace X] in
/-- **`Lᵖ` bounds on an open set from bounds on its compact subsets.** If `f` has `Lᵖ` seminorm at
most `C` on every compact subset of an open set `U`, then it has `Lᵖ` seminorm at most `C` on `U`.
-/
theorem eLpNorm_restrict_le_of_forall_isCompact (hU : IsOpen U) {f : X → F} {C : ℝ≥0∞}
    (h : ∀ K, IsCompact K → K ⊆ U → eLpNorm f p (μ.restrict K) ≤ C) :
    eLpNorm f p (μ.restrict U) ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hC
  · exact le_top
  obtain ⟨K, hKc, hKU, hKm, hKun⟩ := exists_monotone_isCompact_iUnion_eq hU
  have h' : ∀ n, eLpNorm f p (μ.restrict (K n)) ≤ C := fun n => h (K n) (hKc n) (hKU n)
  -- `f` is measurable on each `K n`, where its seminorm is finite, hence on `U`.
  have hm : ∀ n, AEStronglyMeasurable f (μ.restrict (K n)) := fun n =>
    aestronglyMeasurable_of_eLpNorm_ne_top ((h' n).trans_lt hC.lt_top).ne
  have hf : AEStronglyMeasurable f (μ.restrict U) := hKun ▸ aestronglyMeasurable_iUnion_iff.2 hm
  rcases eq_or_ne p 0 with rfl | hp0
  · exact (eLpNorm_exponent_zero hf).trans_le zero_le
  rcases eq_or_ne p ∞ with rfl | hp
  · -- For `p = ∞`, the bound holds almost everywhere on each `K n`, hence on their union.
    rw [eLpNorm_exponent_top hf]
    refine essSup_le_of_ae_le C ?_
    rw [← hKun, EventuallyLE, ae_restrict_iUnion_iff]
    intro n
    filter_upwards [ae_le_eLpNormEssSup (μ := μ.restrict (K n)) (f := f)] with x hx
    exact hx.trans ((eLpNorm_exponent_top (hm n)).symm.trans_le (h' n))
  -- For `p < ∞`, the integral of `‖f‖ᵖ` over `U` is the supremum of its integrals over `K n`.
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hle : ∀ n, ∫⁻ x in K n, ‖f x‖ₑ ^ p.toReal ∂μ ≤ C ^ p.toReal := fun n => by
    have h'' := h' n
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hm n), one_div,
      ENNReal.rpow_inv_le_iff hr] at h''
    exact h''
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf, one_div, ENNReal.rpow_inv_le_iff hr, ← hKun,
    setLIntegral_iUnion_of_directed _ hKm.directed_le]
  exact iSup_le hle

/-- **The tail of an `Lᵖ` function on an open set.** If `f ∈ Lᵖ(U)` for an open set `U` and
`p ≠ ∞`, then for every `ε > 0` there is a compact `K ⊆ U` with `‖f‖_{Lᵖ(U \ K)} ≤ ε`. -/
theorem exists_isCompact_eLpNorm_restrict_sdiff_le (hU : IsOpen U) (hp : p ≠ ∞) {f : X → F}
    (hf : MemLp f p (μ.restrict U)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ K ⊆ U ∧ eLpNorm f p (μ.restrict (U \ K)) ≤ ε := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact ⟨∅, isCompact_empty, empty_subset _, (eLpNorm_exponent_zero
      (hf.aestronglyMeasurable.mono_measure (Measure.restrict_mono sdiff_subset le_rfl))).trans_le
        zero_le⟩
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact ⟨∅, isCompact_empty, empty_subset _, le_top⟩
  obtain ⟨K, hKc, hKU, hKm, hKun⟩ := exists_monotone_isCompact_iUnion_eq hU
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hKm' : ∀ n, MeasurableSet (K n)ᶜ := fun n => (hKc n).isClosed.measurableSet.compl
  -- The integrals of `‖f‖ᵖ` over `U \ K n` tend to zero by dominated convergence.
  have hfin : ∫⁻ x in U, ‖f x‖ₑ ^ p.toReal ∂μ ≠ ∞ := by
    have h := hf.eLpNorm_ne_top
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf.aestronglyMeasurable] at h
    exact fun htop => h (by rw [htop, ENNReal.top_rpow_of_pos (by positivity)])
  have htend : Tendsto (fun n => ∫⁻ x in U, (K n)ᶜ.indicator (fun x => ‖f x‖ₑ ^ p.toReal) x ∂μ)
      atTop (𝓝 0) := by
    rw [← lintegral_zero (μ := μ.restrict U)]
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖f x‖ₑ ^ p.toReal)
      (fun n => (hf.aestronglyMeasurable.eNorm.pow_const p.toReal).indicator (hKm' n))
      (fun n => Eventually.of_forall fun x => indicator_le_self _ _ x) hfin ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [← hKun, mem_iUnion] at hx
    obtain ⟨m, hm⟩ := hx
    exact tendsto_atTop_of_eventually_const (i₀ := m) fun n hn => by
      simp [indicator_of_notMem (notMem_compl_iff.2 (hKm hn hm))]
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds (ENNReal.rpow_pos hε hεt))).exists
  refine ⟨K n, hKc n, hKU n, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
    (hf.aestronglyMeasurable.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)), one_div,
    ENNReal.rpow_inv_le_iff hr]
  refine le_of_eq_of_le ?_ hn.le
  rw [lintegral_indicator (hKm' n), Measure.restrict_restrict (hKm' n), Set.sdiff_eq, inter_comm]

omit [MetricSpace X] [ProperSpace X] [OpensMeasurableSpace X] in
/-- **Splitting an `Lᵖ` seminorm along a set.** For `1 ≤ p` and a measurable set `K`, the `Lᵖ`
seminorm of `f` on `U` is at most the sum of its seminorms on `K` and on `U \ K`. -/
theorem eLpNorm_restrict_le_add_restrict_sdiff (hp : 1 ≤ p) (f : X → F) {K : Set X}
    (hK : MeasurableSet K) :
    eLpNorm f p (μ.restrict U) ≤ eLpNorm f p (μ.restrict K) + eLpNorm f p (μ.restrict (U \ K)) := by
  calc eLpNorm f p (μ.restrict U) = eLpNorm (K.indicator f + Kᶜ.indicator f) p (μ.restrict U) := by
        rw [indicator_self_add_compl]
    _ ≤ eLpNorm (K.indicator f) p (μ.restrict U) + eLpNorm (Kᶜ.indicator f) p (μ.restrict U) :=
        eLpNorm_add_le hp
    _ = eLpNorm f p (μ.restrict (K ∩ U)) + eLpNorm f p (μ.restrict (U \ K)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hK.nullMeasurableSet,
          eLpNorm_indicator_eq_eLpNorm_restrict hK.compl.nullMeasurableSet,
          Measure.restrict_restrict hK, Measure.restrict_restrict hK.compl, Set.sdiff_eq,
          inter_comm U]
    _ ≤ eLpNorm f p (μ.restrict K) + eLpNorm f p (μ.restrict (U \ K)) := by
        gcongr
        exact inter_subset_left

end MeasureTheory
