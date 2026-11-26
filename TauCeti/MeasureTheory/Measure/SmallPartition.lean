/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Finite partitions with small atoms and null boundaries

In a compact pseudometric space with an s-finite measure `μ` on a σ-algebra containing the open
sets, for every `ε > 0` there is a finite measurable partition, given by a label `a : X → Fin n`,
whose atoms have diameter less than `ε` and boundaries of measure zero
(`MeasureTheory.Measure.exists_partition_diam_lt_null_frontier`).

The atoms are built from a finite cover by balls whose frontiers are null: each point is sent to
the first ball of the cover containing it, so the atoms are the `disjointed` sets of the cover.
Each atom is an intersection of a ball with complements of balls, so its frontier is null too
(`TauCeti.null_frontier_disjointed`).

These partitions are the input to the comparison of measure entropy with topological entropy.
-/

public section

open MeasureTheory Metric Set

namespace TauCeti

/-- The `disjointed` sets of a family of sets with null frontiers have null frontiers. -/
theorem null_frontier_disjointed {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [Preorder ι] [LocallyFiniteOrderBot ι] {μ : Measure α} {f : ι → Set α}
    (h : ∀ i, μ (frontier (f i)) = 0) (i : ι) : μ (frontier (disjointed f i)) = 0 := by
  refine disjointedRec (p := fun s ↦ μ (frontier s) = 0) (fun s j hs ↦ ?_) (h i)
  rw [Set.sdiff_eq]
  exact null_frontier_inter hs (by rw [frontier_compl]; exact h j)

end TauCeti

namespace MeasureTheory.Measure

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- **Small partitions with null boundaries.** In a compact pseudometric space with an s-finite
measure, for every `ε > 0` there is a finite measurable partition, given by a label
`a : X → Fin n`, whose atoms have diameter less than `ε` and frontiers of measure zero. -/
theorem exists_partition_diam_lt_null_frontier (μ : Measure X) [SFinite μ] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (n : ℕ) (a : X → Fin n), Measurable a ∧ (∀ i, diam (a ⁻¹' {i}) < ε) ∧
      ∀ i, μ (frontier (a ⁻¹' {i})) = 0 := by
  -- Balls of radius less than `ε / 3` with null frontiers.
  have hr : ∀ x : X, ∃ r ∈ Ioo 0 (ε / 3), μ (frontier (ball x r)) = 0 := fun x ↦ by
    simpa [thickening_singleton] using
      exists_null_frontier_thickening μ {x} (show (0 : ℝ) < ε / 3 by positivity)
  choose r hr0 hrμ using hr
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ball x (r x))
    (fun x ↦ isOpen_ball) fun x _ ↦ mem_iUnion.mpr ⟨x, mem_ball_self (hr0 x).1⟩
  set e := t.equivFin.symm
  set B : Fin t.card → Set X := fun j ↦ ball (e j : X) (r (e j))
  have hB : ∀ x, ∃ j, x ∈ B j := fun x ↦ by
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact ⟨e.symm ⟨c, hc⟩, by simpa [B, e] using hxc⟩
  -- Each point is sent to the first ball containing it; the atoms are the `disjointed` balls.
  classical
  set a : X → Fin t.card := fun x ↦ Fin.find (x ∈ B ·) (hB x)
  have ha : ∀ j, a ⁻¹' {j} = disjointed B j := fun j ↦ by
    rw [disjointed_eq_inter_compl]
    ext x
    simp [a, Fin.find_eq_iff]
  have hmeas : ∀ j, MeasurableSet (a ⁻¹' {j}) := fun j ↦ by
    rw [ha, disjointed_eq_inter_compl]
    exact measurableSet_ball.inter (.iInter fun l ↦ .iInter fun _ ↦ measurableSet_ball.compl)
  refine ⟨t.card, a, measurable_to_countable' hmeas, fun j ↦ ?_, fun j ↦ ?_⟩
  · -- Each atom lies in a ball of radius less than `ε / 3`.
    have hsub : a ⁻¹' {j} ⊆ B j := by
      rw [ha]
      exact disjointed_subset B j
    calc diam (a ⁻¹' {j}) ≤ diam (B j) := diam_mono hsub isBounded_ball
      _ ≤ 2 * r (e j) := diam_ball (hr0 _).1.le
      _ < ε := by linarith [(hr0 (e j : X)).2]
  · -- Each atom is a ball minus earlier balls, all with null frontiers.
    rw [ha]
    exact TauCeti.null_frontier_disjointed (fun _ ↦ hrμ _) j

end MeasureTheory.Measure
