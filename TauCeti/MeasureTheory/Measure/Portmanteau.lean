/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Null-boundary thickenings and finite partitions

The portmanteau theorem makes the masses of a set converge along weak convergence as soon as the
limit law does not charge the boundary of the set. Mathlib's `exists_null_frontier_thickening`
supplies, for one set, thickening radii in any interval whose thickenings have null boundary. This
file chooses a single radius that works simultaneously for countably many sets. It then uses this
to cut a separable space into finitely many continuity sets of small diameter, apart from one set
of arbitrarily small probability.

## Main statements

* `MeasureTheory.Measure.exists_forall_null_frontier_thickening` — for countably many sets, some
  radius in any nonempty open interval gives thickenings whose boundaries are all null.
* `TauCeti.exists_partition_null_frontier_small_last` — a probability measure on a separable
  pseudometric space admits a finite measurable partition into null-boundary sets, all but the last
  lying in balls of a prescribed radius and the last having arbitrarily small measure.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- For countably many sets `s k` and an s-finite measure `μ`, some radius in any nonempty open
interval gives thickenings whose boundaries are all `μ`-null: for each set only countably many
radii fail, and a nonempty open interval of reals is uncountable. -/
theorem exists_forall_null_frontier_thickening (μ : Measure Ω) [SFinite μ] {ι : Type*}
    [Countable ι] (s : ι → Set Ω) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, ∀ k, μ (frontier (Metric.thickening r (s k))) = 0 := by
  have hcount (k : ι) : {r : ℝ | 0 < μ (frontier (Metric.thickening r (s k)))}.Countable :=
    countable_meas_pos_of_disjoint_iUnion (fun r ↦ isClosed_frontier.measurableSet)
      (Metric.frontier_thickening_disjoint (s k))
  obtain ⟨r, hr, hr'⟩ :
      (Ioo a b \ ⋃ k, {r : ℝ | 0 < μ (frontier (Metric.thickening r (s k)))}).Nonempty := by
    refine nonempty_of_not_subset fun hsub ↦ ?_
    exact (Cardinal.Real.Ioo_countable_iff.1 ((countable_iUnion hcount).mono hsub)).not_gt hab
  refine ⟨r, hr, fun k ↦ ?_⟩
  by_contra hk
  exact hr' (mem_iUnion.2 ⟨k, pos_iff_ne_zero.2 hk⟩)

end MeasureTheory.Measure

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.SeparableSpace X]

/-- A finite partition of `X` into pieces of `μ`-null boundary: all but the last piece lie in
balls of radius `r`, and the last piece has `μ`-mass at most `ε`. -/
theorem exists_partition_null_frontier_small_last (μ : Measure X) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (N : ℕ) (A : Fin (N + 1) → Set X), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = univ ∧ (∀ i, μ (frontier (A i)) = 0) ∧
      (∀ i : Fin (N + 1), i ≠ Fin.last N → ∃ x, A i ⊆ Metric.ball x r) ∧
      μ (A (Fin.last N)) ≤ ε := by
  have := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨ρ, ⟨hρ0, hρr⟩, hρ⟩ := μ.exists_forall_null_frontier_thickening (fun k ↦ {u k}) hr
  simp only [Metric.thickening_singleton] at hρ
  -- The union of the first `N` balls exhausts the space, so its complement becomes small.
  set G : ℕ → Set X := fun N ↦ ⋃ k < N, Metric.ball (u k) ρ
  have hG : Tendsto (fun N ↦ μ (G N)ᶜ) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun N ↦ (G N)ᶜ)
      (fun N ↦ (MeasurableSet.biUnion (to_countable _)
        fun _ _ ↦ measurableSet_ball).compl.nullMeasurableSet)
      (fun M N hMN ↦ compl_subset_compl.2 <| biUnion_subset_biUnion_left fun k hk ↦
        lt_of_lt_of_le hk hMN) ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ N, (G N)ᶜ = ∅ := by
      rw [← compl_iUnion, compl_empty_iff, eq_univ_iff_forall]
      intro x
      obtain ⟨k, hk⟩ := (Metric.denseRange_iff.1 hu) x ρ hρ0
      exact mem_iUnion.2 ⟨k + 1, mem_iUnion₂.2 ⟨k, Nat.lt_succ_self k, Metric.mem_ball.2 hk⟩⟩
    simpa only [Function.comp_def, hempty, measure_empty] using hlim
  obtain ⟨N, hN⟩ := (hG.eventually (ge_mem_nhds hε)).exists
  -- The cells: the first `N` balls made disjoint, followed by the rest of the space.
  set f : Fin (N + 1) → Set X := fun i ↦
    if (i : ℕ) < N then Metric.ball (u i) ρ else univ with hf
  have hfm (i : Fin (N + 1)) : MeasurableSet (f i) := by
    simp only [hf]
    split_ifs
    exacts [measurableSet_ball, MeasurableSet.univ]
  have hff (i : Fin (N + 1)) : μ (frontier (f i)) = 0 := by
    simp only [hf]
    split_ifs
    exacts [hρ _, by simp]
  refine ⟨N, disjointed f, fun i ↦ disjointedRec (p := MeasurableSet)
    (fun t j ht ↦ ht.diff (hfm j)) (hfm i), disjoint_disjointed f, ?_, fun i ↦ ?_, fun i hi ↦ ?_,
    ?_⟩
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    exact fun x ↦ mem_iUnion.2 ⟨Fin.last N, by simp [hf]⟩
  · refine disjointedRec (p := fun t ↦ μ (frontier t) = 0) (fun t j ht ↦ ?_) (hff i)
    rw [sdiff_eq]
    exact null_frontier_inter ht (by rw [frontier_compl]; exact hff j)
  · have hiN : (i : ℕ) < N := by simpa using Fin.val_lt_last hi
    refine ⟨u i, (disjointed_subset f i).trans ?_⟩
    simp only [hf, hiN, ite_true]
    exact Metric.ball_subset_ball hρr.le
  · refine le_trans (measure_mono fun x hx ↦ ?_) hN
    rw [disjointed_eq_inter_compl] at hx
    simp only [mem_inter_iff, mem_iInter, mem_compl_iff] at hx
    simp only [G, mem_compl_iff, mem_iUnion, not_exists]
    intro k hk hxk
    refine hx.2 ⟨k, by omega⟩ (Fin.mk_lt_of_lt_val (by simpa using hk)) ?_
    simp [hf, hk, hxk]

end TauCeti
