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
(`TauCeti.exists_label_diam_lt_measure_frontier_eq_zero`).

The atoms are built from a finite cover by balls whose spheres are null: each point is sent to the
first ball of the cover containing it, so the atoms are the `disjointed` sets of the cover. Off
the union of the frontiers of the balls the label is locally constant, so every atom has its
frontier in that null union.

These partitions are the input to the comparison of measure entropy with topological entropy.

## References

* The statement is in the roadmap ArithmeticDynamics, §2.7, Measure entropy and maximizing
  measures (finite Borel partitions with atom diameters less than `ε` and `μ`-null boundaries,
  by finite covers by balls whose spheres have zero measure).
-/

public section

open MeasureTheory Metric Set Filter Topology

namespace TauCeti

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- Off the frontier of a set, membership in the set is locally constant. -/
theorem eventually_mem_iff_of_notMem_frontier {s : Set X} {x : X} (hx : x ∉ frontier s) :
    ∀ᶠ y in 𝓝 x, (y ∈ s ↔ x ∈ s) := by
  by_cases hxs : x ∈ s
  · have : x ∈ interior s := by
      by_contra h
      exact hx ⟨subset_closure hxs, h⟩
    filter_upwards [mem_interior_iff_mem_nhds.mp this] with y hy
    simp [hy, hxs]
  · have : x ∈ interior sᶜ := by
      rw [interior_compl]
      intro h
      exact hx ⟨h, fun h' ↦ hxs (interior_subset h')⟩
    filter_upwards [mem_interior_iff_mem_nhds.mp this] with y hy
    simp [hxs, show y ∉ s from hy]

/-- If a label is locally constant at `x`, then `x` is not in the frontier of any of its
fibres. -/
theorem notMem_frontier_preimage_singleton_of_eventually {ι : Type*} {a : X → ι} {x : X}
    (hx : ∀ᶠ y in 𝓝 x, a y = a x) (i : ι) : x ∉ frontier (a ⁻¹' {i}) := by
  by_cases hi : a x = i
  · subst hi
    have : x ∈ interior (a ⁻¹' {a x}) := mem_interior_iff_mem_nhds.mpr hx
    exact fun h ↦ h.2 this
  · have : x ∈ interior (a ⁻¹' {i})ᶜ := by
      refine mem_interior_iff_mem_nhds.mpr ?_
      filter_upwards [hx] with y hy
      simp [hy, hi]
    rw [interior_compl] at this
    exact fun h ↦ this h.1

end Topology

section FirstIndex

variable {X : Type*}

/-- For a finite family of sets covering `X`, the label sending a point to the first set
containing it. -/
private noncomputable def firstIndex {n : ℕ} (B : Fin n → Set X) (hB : ∀ x, ∃ j, x ∈ B j)
    (x : X) : Fin n :=
  open scoped Classical in
  (Finset.univ.filter fun j ↦ x ∈ B j).min'
    (let ⟨j, hj⟩ := hB x; ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)

private theorem firstIndex_mem {n : ℕ} (B : Fin n → Set X) (hB : ∀ x, ∃ j, x ∈ B j) (x : X) :
    x ∈ B (firstIndex B hB x) := by
  classical
  unfold firstIndex
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter fun j ↦ x ∈ B j) _)).2

private theorem firstIndex_le {n : ℕ} (B : Fin n → Set X) (hB : ∀ x, ∃ j, x ∈ B j) {x : X}
    {j : Fin n} (hj : x ∈ B j) : firstIndex B hB x ≤ j := by
  classical
  unfold firstIndex
  exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

/-- The fibres of the first-index label are the disjointed sets of the cover. -/
private theorem firstIndex_preimage {n : ℕ} (B : Fin n → Set X) (hB : ∀ x, ∃ j, x ∈ B j)
    (j : Fin n) : firstIndex B hB ⁻¹' {j} = disjointed B j := by
  rw [disjointed_eq_inter_compl]
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, mem_compl_iff]
  constructor
  · rintro rfl
    exact ⟨firstIndex_mem B hB x, fun l hl hx ↦ (firstIndex_le B hB hx).not_gt hl⟩
  · rintro ⟨hj, hlt⟩
    refine le_antisymm (firstIndex_le B hB hj) (not_lt.mp fun h ↦ ?_)
    exact hlt _ h (firstIndex_mem B hB x)

end FirstIndex

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- **Small partitions with null boundaries.** In a compact pseudometric space with an s-finite
measure, for every `ε > 0` there is a finite measurable label whose atoms have diameter less than
`ε` and frontiers of measure zero. -/
theorem exists_label_diam_lt_measure_frontier_eq_zero (μ : Measure X) [SFinite μ] {ε : ℝ}
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
  set a := firstIndex B hB
  have hmeas : ∀ j, MeasurableSet (a ⁻¹' {j}) := fun j ↦ by
    rw [firstIndex_preimage, disjointed_eq_inter_compl]
    exact measurableSet_ball.inter (.iInter fun l ↦ .iInter fun _ ↦ measurableSet_ball.compl)
  refine ⟨t.card, a, measurable_to_countable' hmeas, fun j ↦ ?_, fun j ↦ ?_⟩
  · -- Each atom lies in a ball of radius less than `ε / 3`.
    have hsub : a ⁻¹' {j} ⊆ B j := fun x hx ↦ by
      have := firstIndex_mem B hB x
      rwa [show firstIndex B hB x = j from hx] at this
    calc diam (a ⁻¹' {j}) ≤ diam (B j) := diam_mono hsub isBounded_ball
      _ ≤ 2 * r (e j) := diam_ball (hr0 _).1.le
      _ < ε := by linarith [(hr0 (e j : X)).2]
  · -- Off the null union of the frontiers of the balls, the label is locally constant.
    refine measure_mono_null (t := ⋃ l, frontier (B l)) (fun x hx ↦ ?_)
      (measure_iUnion_null fun l ↦ hrμ _)
    by_contra hxU
    simp only [mem_iUnion, not_exists] at hxU
    have hev : ∀ᶠ y in 𝓝 x, ∀ l, (y ∈ B l ↔ x ∈ B l) :=
      eventually_all.mpr fun l ↦ eventually_mem_iff_of_notMem_frontier (hxU l)
    refine notMem_frontier_preimage_singleton_of_eventually ?_ j hx
    filter_upwards [hev] with y hy
    exact le_antisymm (firstIndex_le B hB ((hy _).mpr (firstIndex_mem B hB x)))
      (firstIndex_le B hB ((hy _).mp (firstIndex_mem B hB y)))

end TauCeti
