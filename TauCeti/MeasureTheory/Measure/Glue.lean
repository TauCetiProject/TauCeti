/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Gluing measures along a cover

A family of measures prescribed on the members of a family of measurable sets, agreeing on
overlaps, comes from a single measure as soon as countably many of the sets cover the
space, and that measure is unique. This is the descent step for measures that are only defined
locally, such as the Riemannian volume, which is given chart by chart.

## Main results

* `TauCeti.existsUnique_restrict_eq`: compatible measures on a family of measurable
  sets with a countable subcover glue to a unique measure.
* `TauCeti.measure_image_eq_of_locally_eq`: on a hereditarily Lindelöf space, if a map carries
  `μ` to `ν` on the measurable subsets of a neighbourhood of each point of a measurable set `s`,
  then it does so on `s`.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Set
open scoped Topology

namespace TauCeti

variable {α ι : Type*} [MeasurableSpace α]

/-- Measures `μ i` prescribed on measurable sets `s i` are the restrictions of a unique measure,
provided that the sets `s i` with `i` in a countable index set `t` cover the space, and that each
such `μ i` agrees with every `μ j` on the overlap `s i ∩ s j`. The overlap condition is necessary,
and every `s i` is matched, not only those of the countable subcover. -/
theorem existsUnique_restrict_eq {s : ι → Set α} {μ : ι → Measure α}
    (hs : ∀ i, MeasurableSet (s i)) {t : Set ι} (ht : t.Countable) (hcover : ⋃ i ∈ t, s i = univ)
    (h : ∀ i ∈ t, ∀ j, (μ i).restrict (s i ∩ s j) = (μ j).restrict (s i ∩ s j)) :
    ∃! ν : Measure α, ∀ i, ν.restrict (s i) = (μ i).restrict (s i) := by
  refine existsUnique_of_exists_of_unique ?_ fun ν ν' hν hν' ↦
    ext_of_biUnion_eq_univ ht hcover fun i _ ↦ (hν i).trans (hν' i).symm
  obtain rfl | htne := t.eq_empty_or_nonempty
  · have : IsEmpty α := univ_eq_empty_iff.1 (by simpa [eq_comm] using hcover)
    exact ⟨0, fun i ↦ Subsingleton.elim _ _⟩
  -- Enumerate the countable subcover and sum the prescribed measures over its disjointed pieces.
  obtain ⟨f, rfl⟩ := ht.exists_eq_range htne
  set d := disjointed fun n ↦ s (f n) with hd_def
  have hd : ∀ n, MeasurableSet (d n) := MeasurableSet.disjointed fun n ↦ hs (f n)
  have hdcover : ⋃ n, d n = univ := by rw [hd_def, iUnion_disjointed, ← biUnion_range, hcover]
  refine ⟨sum fun n ↦ (μ (f n)).restrict (d n), fun j ↦ ?_⟩
  -- On each piece `d n ⊆ s (f n)`, the prescribed measure `μ (f n)` agrees with `μ j` on `s j`.
  have hpiece (n : ℕ) : ((μ (f n)).restrict (d n)).restrict (s j) = (μ j).restrict (s j ∩ d n) := by
    have hsub : s j ∩ d n ⊆ s (f n) ∩ s j :=
      fun y hy ↦ ⟨disjointed_subset _ n hy.2, hy.1⟩
    rw [restrict_restrict (hs j), ← restrict_restrict_of_subset hsub, h (f n) (mem_range_self n) j,
      restrict_restrict_of_subset hsub]
  have hdisj : Pairwise (Disjoint on fun n ↦ s j ∩ d n) :=
    (disjoint_disjointed _).mono fun _ _ hmn ↦ hmn.mono inter_subset_right inter_subset_right
  rw [restrict_sum _ (hs j), funext hpiece, ← restrict_iUnion hdisj fun n ↦ (hs j).inter (hd n),
    ← inter_iUnion, hdcover, inter_univ]

/-- **Image measures from local pieces.** Let `M` be a hereditarily Lindelöf space in which open
sets are measurable, `s` a measurable subset of `M` and `Φ : M → Y` a map whose restriction to `s`
is a measurable embedding. If each point `x` of `s` has a neighbourhood `U x` such that
`ν (Φ '' u) = μ u` for every measurable `u ⊆ s` contained in `U x`, then `ν (Φ '' s) = μ s`.
Countably many of the neighbourhoods cover `s`, so the measures `t ↦ ν (Φ '' t)` and `t ↦ μ t` on
the subtype `s` agree. -/
theorem measure_image_eq_of_locally_eq {M Y : Type*} [TopologicalSpace M]
    [HereditarilyLindelofSpace M] [MeasurableSpace M] [OpensMeasurableSpace M] [MeasurableSpace Y]
    {μ : Measure M} {ν : Measure Y} {Φ : M → Y} {s : Set M} (hs : MeasurableSet s)
    (he : MeasurableEmbedding (s.domRestrict Φ)) {U : M → Set M} (hU : ∀ x ∈ s, U x ∈ 𝓝 x)
    (h : ∀ x ∈ s, ∀ u, MeasurableSet u → u ⊆ s → u ⊆ U x → ν (Φ '' u) = μ u) :
    ν (Φ '' s) = μ s := by
  have hι : MeasurableEmbedding (Subtype.val : s → M) := .subtypeVal hs
  obtain ⟨T, hTc, hTs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_nhds_subcover
    (fun x ↦ interior (U x)) fun x hx ↦ interior_mem_nhds.2 (hU x hx)
  have himage (t : Set s) : s.domRestrict Φ '' t = Φ '' (Subtype.val '' t) := by
    rw [domRestrict_eq, image_comp]
  suffices hcomap : ν.comap (s.domRestrict Φ) = μ.comap Subtype.val by
    calc ν (Φ '' s) = ν.comap (s.domRestrict Φ) univ := by
          rw [he.comap_apply, image_univ, range_domRestrict]
      _ = μ s := by rw [hcomap, hι.comap_apply, image_univ, Subtype.range_coe]
  refine ext_of_biUnion_eq_univ (s := fun x ↦ (Subtype.val : s → M) ⁻¹' interior (U x)) hTc
    (by rw [← preimage_iUnion₂]; exact eq_univ_of_forall fun y ↦ hcover y.property)
    fun x hx ↦ ?_
  ext t ht
  have htU : MeasurableSet (t ∩ Subtype.val ⁻¹' interior (U x)) :=
    ht.inter (isOpen_interior.measurableSet.preimage measurable_subtypeVal)
  rw [restrict_apply ht, restrict_apply ht, he.comap_apply, hι.comap_apply, himage]
  exact h x (hTs x hx) _ (hι.measurableSet_image' htU) (Subtype.coe_image_subset s _)
    (by rintro _ ⟨y, hy, rfl⟩; exact interior_subset hy.2)

end TauCeti
