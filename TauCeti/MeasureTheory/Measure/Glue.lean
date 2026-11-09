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
overlaps, comes from a single measure as soon as countably many of the sets cover the
space, and that measure is unique. This is the descent step for measures that are only defined
locally, such as the Riemannian volume, which is given chart by chart.

## Main results

* `TauCeti.existsUnique_restrict_eq`: compatible measures on a family of measurable
  sets with a countable subcover glue to a unique measure.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Set

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

end TauCeti
