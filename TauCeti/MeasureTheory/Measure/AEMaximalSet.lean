/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# An almost-everywhere largest member of a family closed under countable unions

Let `C` be a nonempty family of measurable sets that is closed under countable unions, and let `μ`
be an s-finite measure. Then `C` has a member `t` that contains every member of `C` up to a
`μ`-null set. When `μ` is finite, `t` is a member of maximal measure: take members whose measures
tend to the supremum of the measures of the members, and let `t` be their union. A member `s`
with `μ (s \ t) ≠ 0` would make `s ∪ t` a member of larger measure. The s-finite case reduces to
the finite one through Mathlib's equivalent finite measure `μ.toFinite`.

This is the exhaustion step behind the Halmos–Savage lemma on dominated families of measures,
where it is applied to the null sets of one measure and to the unions of the supports of countably
many measures.

## Main results

* `MeasureTheory.exists_mem_forall_ae_le_of_iUnion_mem`: a nonempty family of measurable sets
  closed under countable unions has a member that a.e. contains every member.

## References

* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), proof of Lemma 1.2.1.
-/

public section

open Set Filter Topology

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {C : Set (Set α)}

/-- The finite case of `exists_mem_forall_ae_le_of_iUnion_mem`: a member of maximal measure. -/
private theorem exists_mem_forall_ae_le_of_iUnion_mem_of_isFiniteMeasure [IsFiniteMeasure μ]
    (hC_meas : ∀ s ∈ C, MeasurableSet s) (hC : C.Nonempty)
    (hC_iUnion : ∀ s : ℕ → Set α, (∀ n, s n ∈ C) → ⋃ n, s n ∈ C) :
    ∃ t ∈ C, ∀ s ∈ C, s ≤ᵐ[μ] t := by
  -- Members whose measures tend to the supremum of the measures of members.
  obtain ⟨u, -, hu_lim, hu_mem⟩ :=
    exists_seq_tendsto_sSup (hC.image μ) (OrderTop.bddAbove (μ '' C))
  choose s hsC hsμ using hu_mem
  -- Their union `t` is a member of maximal measure.
  set t := ⋃ n, s n
  have htC : t ∈ C := hC_iUnion s hsC
  have hle : ∀ v ∈ C, μ v ≤ μ t := by
    refine fun v hv ↦ (le_sSup (mem_image_of_mem μ hv)).trans ?_
    refine le_of_tendsto' hu_lim fun n ↦ ?_
    rw [← hsμ n]
    exact measure_mono (subset_iUnion s n)
  refine ⟨t, htC, fun v hv ↦ ?_⟩
  -- `v ∪ t` is a member, so its measure is at most that of `t`, and `v \ t` is null.
  let w : ℕ → Set α := fun n ↦ Nat.casesOn n v s
  have hwC : ∀ n, w n ∈ C := fun n ↦ by cases n <;> simp [w, hv, hsC]
  have hvt : ⋃ n, w n = v ∪ t := (union_iUnion_nat_succ w).symm
  have hdiff : μ (v \ t) = 0 := by
    have hmeas := hle _ (hC_iUnion w hwC)
    rw [hvt] at hmeas
    rw [← union_sdiff_right, measure_sdiff subset_union_right
      (hC_meas t htC).nullMeasurableSet (measure_ne_top μ t)]
    exact tsub_eq_zero_of_le hmeas
  exact ae_subset.mpr hdiff

/-- A nonempty family `C` of measurable sets that is closed under countable unions has a member
`t` containing every member of `C` up to a `μ`-null set, for any s-finite measure `μ`. -/
theorem exists_mem_forall_ae_le_of_iUnion_mem [SFinite μ]
    (hC_meas : ∀ s ∈ C, MeasurableSet s) (hC : C.Nonempty)
    (hC_iUnion : ∀ s : ℕ → Set α, (∀ n, s n ∈ C) → ⋃ n, s n ∈ C) :
    ∃ t ∈ C, ∀ s ∈ C, s ≤ᵐ[μ] t := by
  obtain ⟨t, htC, ht⟩ :=
    exists_mem_forall_ae_le_of_iUnion_mem_of_isFiniteMeasure (μ := μ.toFinite) hC_meas hC
      hC_iUnion
  exact ⟨t, htC, fun s hs ↦ ae_toFinite (μ := μ) ▸ ht s hs⟩

end MeasureTheory
