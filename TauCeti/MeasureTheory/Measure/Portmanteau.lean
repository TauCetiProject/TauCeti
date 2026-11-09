/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Continuity sets, null-boundary thickenings and finite partitions

The portmanteau theorem makes the masses of a set converge along weak convergence as soon as the
limit law does not charge the boundary of the set. Mathlib's `exists_null_frontier_thickening`
supplies, for one set, thickening radii in any interval whose thickenings have null boundary. This
file chooses a single radius that works simultaneously for countably many sets. It then uses this
to cut a separable space into finitely many continuity sets of small diameter, apart from one set
of arbitrarily small probability.

Weak convergence of finite measures also implies convergence of their masses on sets with
null boundary, including when the limit measure is zero. This extends the probability-measure
portmanteau API and is useful when localizing locally finite measures.

## Main statements

* `MeasureTheory.FiniteMeasure.tendsto_measure_of_null_frontier_of_tendsto` — weak convergence
  of finite measures implies convergence on every continuity set of the limit measure.

* `MeasureTheory.Measure.exists_forall_null_frontier_thickening` — for countably many sets, some
  radius in any nonempty open interval gives thickenings whose boundaries are all null.
* `MeasureTheory.Measure.exists_partition_null_frontier_small_last` — a finite measure on a
  separable pseudometric space admits a finite measurable partition into null-boundary sets, all but
  the last lying in balls of a prescribed radius and the last having arbitrarily small measure.
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

/-- For a dense sequence `u` and a radius `ρ > 0`, the complement of the union of the first `N`
balls of radius `ρ` around the points `u k` has measure tending to `0` as `N → ∞`. -/
theorem tendsto_measure_compl_biUnion_lt_ball {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {u : ℕ → X} (hu : DenseRange u)
    {ρ : ℝ} (hρ0 : 0 < ρ) :
    Tendsto (fun N ↦ μ (⋃ k < N, Metric.ball (u k) ρ)ᶜ) atTop (𝓝 0) := by
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun N ↦ (⋃ k < N, Metric.ball (u k) ρ)ᶜ)
    (fun N ↦ (MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_ball).compl.nullMeasurableSet)
    (fun M N hMN ↦ compl_subset_compl.2 <| iUnion_mono fun _ ↦
      iUnion_subset_iUnion_const fun hk ↦ lt_of_lt_of_le hk hMN) ⟨0, measure_ne_top _ _⟩
  have hempty : ⋂ N, (⋃ k < N, Metric.ball (u k) ρ)ᶜ = ∅ := by
    rw [← compl_iUnion, compl_empty_iff, eq_univ_iff_forall]
    intro x
    obtain ⟨k, hk⟩ := (Metric.denseRange_iff.1 hu) x ρ hρ0
    exact mem_iUnion.2 ⟨k + 1, mem_iUnion₂.2 ⟨k, Nat.lt_succ_self k, Metric.mem_ball.2 hk⟩⟩
  simpa only [Function.comp_def, hempty, measure_empty] using hlim

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.SeparableSpace X]

/-- A finite partition of `X` into pieces of `μ`-null boundary: all but the last piece lie in
balls of radius `r`, and the last piece has `μ`-mass at most `ε`. -/
theorem exists_partition_null_frontier_small_last (μ : Measure X) [IsFiniteMeasure μ] {r : ℝ}
    (hr : 0 < r) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (N : ℕ) (A : Fin (N + 1) → Set X), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = univ ∧ (∀ i, μ (frontier (A i)) = 0) ∧
      (∀ i : Fin (N + 1), i ≠ Fin.last N → ∃ x, A i ⊆ Metric.ball x r) ∧
      μ (A (Fin.last N)) ≤ ε := by
  -- On the empty space the single cell `univ` is null.
  cases isEmpty_or_nonempty X
  · refine ⟨0, fun _ ↦ univ, fun _ ↦ .univ,
      fun i j hij ↦ (hij (Subsingleton.elim (α := Fin 1) i j)).elim, iUnion_const _,
      fun _ ↦ by simp, fun i hi ↦ (hi (Subsingleton.elim (α := Fin 1) _ _)).elim, ?_⟩
    simp [univ_eq_empty_iff.2 ‹IsEmpty X›]
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨ρ, ⟨hρ0, hρr⟩, hρ⟩ := μ.exists_forall_null_frontier_thickening (fun k ↦ {u k}) hr
  simp only [Metric.thickening_singleton] at hρ
  -- The union of the first `N` balls exhausts the space, so its complement becomes small.
  set G : ℕ → Set X := fun N ↦ ⋃ k < N, Metric.ball (u k) ρ
  have hG : Tendsto (fun N ↦ μ (G N)ᶜ) atTop (𝓝 0) :=
    tendsto_measure_compl_biUnion_lt_ball μ hu hρ0
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
    rw [Set.sdiff_eq]
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

end MeasureTheory.Measure

namespace MeasureTheory.FiniteMeasure

variable {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] [HasOuterApproxClosed X] {l : Filter ι}
  {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}

/-- Weak convergence of finite measures gives convergence on every continuity set of the
limit measure. No measurability assumption on the set is needed. -/
theorem tendsto_measure_of_null_frontier_of_tendsto
    (h : Tendsto μs l (𝓝 μ)) {s : Set X} (hs : (μ : Measure X) (frontier s) = 0) :
    Tendsto (fun i ↦ (μs i : Measure X) s) l (𝓝 ((μ : Measure X) s)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simpa only [Set.eq_empty_of_isEmpty s, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))
  by_cases hμ : μ = 0
  · subst μ
    simp only [toMeasure_zero, FunLike.coe_zero, Pi.zero_apply]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [Function.comp_def, ennreal_mass, zero_mass, ENNReal.coe_zero] using
        (ENNReal.continuous_coe.tendsto _).comp h.mass)
      (fun _ ↦ bot_le) (fun _ ↦ measure_mono (subset_univ s))
  · have hn := tendsto_normalize_of_tendsto h hμ
    have hboundary : (μ.normalize : Measure X) (frontier s) = 0 := by
      simp [toMeasure_normalize_eq_of_ne_zero μ hμ, hs]
    have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn
      (by simpa only [ProbabilityMeasure.null_iff_toMeasure_null] using hboundary)
    have hprod := h.mass.mul hp
    simp_rw [← self_eq_mass_mul_normalize] at hprod
    simpa only [Function.comp_def, ennreal_coeFn_eq_coeFn_toMeasure] using
      (ENNReal.continuous_coe.tendsto _).comp hprod

end MeasureTheory.FiniteMeasure
