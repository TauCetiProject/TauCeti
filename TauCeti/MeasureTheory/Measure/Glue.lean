/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Gluing measures along a cover

A family of measures prescribed on the members of a family of measurable sets, agreeing on
pairwise overlaps, comes from a single measure as soon as countably many of the sets cover the
space, and that measure is unique. This is the descent step for measures that are only defined
locally, such as the Riemannian volume, which is given chart by chart.

Existence restricts the prescribed measures to the disjointed pieces of an enumeration of the
countable subcover and sums them; uniqueness is `MeasureTheory.Measure.ext_of_biUnion_eq_univ`.

## Main results

* `MeasureTheory.Measure.existsUnique_restrict_eq`: compatible measures on a family of measurable
  sets with a countable subcover glue to a unique measure.
-/

public section

open Function Set

namespace MeasureTheory.Measure

variable {α ι : Type*} [MeasurableSpace α]

/-- Measures `μ i` prescribed on measurable sets `s i`, agreeing on the pairwise overlaps, are the
restrictions of a unique measure, provided that countably many of the sets `s i` cover the space.
The overlap condition is necessary, and every `s i` is matched, not only those of the countable
subcover. -/
theorem existsUnique_restrict_eq {s : ι → Set α} {μ : ι → Measure α}
    (hs : ∀ i, MeasurableSet (s i)) {t : Set ι} (ht : t.Countable) (hcover : ⋃ i ∈ t, s i = univ)
    (h : ∀ i j, (μ i).restrict (s i ∩ s j) = (μ j).restrict (s i ∩ s j)) :
    ∃! ν : Measure α, ∀ i, ν.restrict (s i) = (μ i).restrict (s i) := by
  refine existsUnique_of_exists_of_unique ?_ fun ν ν' hν hν' ↦
    ext_of_biUnion_eq_univ ht hcover fun i _ ↦ (hν i).trans (hν' i).symm
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x⟩⟩
  · exact ⟨0, fun i ↦ Subsingleton.elim _ _⟩
  -- Enumerate the countable subcover and sum the prescribed measures over its disjointed pieces.
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (hcover.symm ▸ mem_univ x : x ∈ ⋃ i ∈ t, s i)
    exact ⟨i, hi⟩
  obtain ⟨f, rfl⟩ := ht.exists_eq_range htne
  have hfcover : ⋃ n, s (f n) = univ := by rwa [biUnion_range] at hcover
  set d := disjointed fun n ↦ s (f n) with hd_def
  have hd : ∀ n, MeasurableSet (d n) := MeasurableSet.disjointed fun n ↦ hs (f n)
  have hdcover : ⋃ n, d n = univ := by rw [hd_def, iUnion_disjointed, hfcover]
  refine ⟨sum fun n ↦ (μ (f n)).restrict (d n), fun j ↦ ?_⟩
  -- On each piece `d n ⊆ s (f n)`, the prescribed measure `μ (f n)` agrees with `μ j` on `s j`.
  have hpiece (n : ℕ) : ((μ (f n)).restrict (d n)).restrict (s j) = (μ j).restrict (s j ∩ d n) := by
    have hsub : s j ∩ d n ⊆ s (f n) ∩ s j :=
      fun y hy ↦ ⟨disjointed_subset _ n hy.2, hy.1⟩
    rw [restrict_restrict (hs j), ← restrict_restrict_of_subset hsub, h (f n) j,
      restrict_restrict_of_subset hsub]
  have hdisj : Pairwise (Disjoint on fun n ↦ s j ∩ d n) :=
    (disjoint_disjointed _).mono fun _ _ hmn ↦ hmn.mono inter_subset_right inter_subset_right
  rw [restrict_sum _ (hs j), funext hpiece, ← restrict_iUnion hdisj fun n ↦ (hs j).inter (hd n),
    ← inter_iUnion, hdcover, inter_univ]

end MeasureTheory.Measure
