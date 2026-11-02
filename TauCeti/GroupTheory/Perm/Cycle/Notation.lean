/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Disjoint cycle notation

A permutation of a finite type is written in *disjoint cycle notation* as a list of cycles, each
cycle a list of points traversed in order, such that no point is listed twice and every cycle has
at least two points. Fixed points are omitted, and the identity is the empty list of cycles. The
cycle `l` denotes `List.formPerm l`, sending each listed point to the next and the last back to
the first, and the notation denotes the product of its cycles. The cycles are
disjoint, so they commute and the product does not depend on their order.

`Equiv.Perm.IsCycleNotation σ p` says that `p` is a disjoint cycle notation for `σ`. The lengths
of the listed cycles are then the cycle type of `σ`, the listed points are its support, and the
full cycle partition of `σ` is recovered by padding the lengths with one part equal to one for
each point not listed. Reversing every cycle gives a notation for the inverse, and every
permutation has a notation.

## Main definitions

* `Equiv.Perm.IsCycleNotation`: `p` is a disjoint cycle notation for `σ`.

## Main results

* `Equiv.Perm.IsCycleNotation.cycleType_eq`: the cycle type is the multiset of listed lengths.
* `Equiv.Perm.IsCycleNotation.parts_partition_eq`: the full cycle partition is the listed
  lengths padded by fixed points.
* `Equiv.Perm.IsCycleNotation.inv`: reversing every cycle writes the inverse.
* `Equiv.Perm.exists_isCycleNotation`: every permutation has a disjoint cycle notation.

## References

The proof of `Equiv.Perm.IsCycleNotation.cycleType_eq` follows the cycle-type computation in the
construction half of Mathlib's `Equiv.Perm.exists_with_cycleType_iff`
(`Mathlib/GroupTheory/Perm/Cycle/PossibleTypes.lean`).
-/

public section

namespace Equiv.Perm

open List

variable {α : Type*} [DecidableEq α]

/-- `p` is a **disjoint cycle notation** for `σ`: no point is listed twice, every listed cycle has
at least two points, and `σ` is the product of the cycles `List.formPerm l` for `l ∈ p`. Fixed
points of `σ` are not listed, and the identity is written as the empty list. -/
structure IsCycleNotation (σ : Perm α) (p : List (List α)) : Prop where
  /-- No point is listed twice. -/
  nodup_flatten : p.flatten.Nodup
  /-- Every listed cycle has at least two points. -/
  two_le_length : ∀ l ∈ p, 2 ≤ l.length
  /-- The permutation is the product of the listed cycles. -/
  prod_map_formPerm : (p.map formPerm).prod = σ

/-- The empty list of cycles writes exactly the identity. -/
@[simp]
theorem isCycleNotation_nil_iff {σ : Perm α} : σ.IsCycleNotation [] ↔ σ = 1 :=
  ⟨fun h ↦ h.prod_map_formPerm.symm, fun h ↦ ⟨nodup_nil, by simp, by simp [h]⟩⟩

namespace IsCycleNotation

variable {σ : Perm α} {p : List (List α)}

/-- Every listed cycle lists distinct points. -/
theorem nodup (h : σ.IsCycleNotation p) {l : List α} (hl : l ∈ p) : l.Nodup :=
  (List.nodup_flatten.mp h.nodup_flatten).1 l hl

/-- The listed cycles are disjoint permutations. -/
theorem pairwise_disjoint (h : σ.IsCycleNotation p) : (p.map formPerm).Pairwise Disjoint := by
  rw [pairwise_map]
  refine (List.nodup_flatten.mp h.nodup_flatten).2.imp_of_mem fun hl hl' hd ↦ ?_
  exact (formPerm_disjoint_iff (h.nodup hl) (h.nodup hl') (h.two_le_length _ hl)
    (h.two_le_length _ hl')).mpr hd

/-- Every listed cycle is a cycle. -/
theorem isCycle_formPerm (h : σ.IsCycleNotation p) {l : List α} (hl : l ∈ p) :
    l.formPerm.IsCycle :=
  List.isCycle_formPerm (h.nodup hl) (h.two_le_length l hl)

/-- Dropping the first cycle of a disjoint cycle notation leaves a notation for the product of the
remaining cycles. -/
theorem of_cons {l : List α} (h : σ.IsCycleNotation (l :: p)) :
    (p.map formPerm).prod.IsCycleNotation p :=
  ⟨(nodup_append.mp (flatten_cons ▸ h.nodup_flatten)).2.1,
    fun l' hl' ↦ h.two_le_length l' (mem_cons_of_mem _ hl'), rfl⟩

/-- A point is moved by `σ` exactly when it is listed. -/
theorem apply_ne_self_iff (h : σ.IsCycleNotation p) {x : α} : σ x ≠ x ↔ x ∈ p.flatten := by
  induction p generalizing σ with
  | nil => simp [isCycleNotation_nil_iff.mp h]
  | cons l p ih =>
    have hl := h.nodup (mem_cons_self ..)
    have hd : Disjoint l.formPerm (p.map formPerm).prod := by
      refine disjoint_prod_right _ fun g hg ↦ ?_
      have := h.pairwise_disjoint
      rw [map_cons, pairwise_cons] at this
      exact this.1 g hg
    have hl1 : ∀ y, l ≠ [y] := fun y hy ↦ by
      simpa [hy] using h.two_le_length l (mem_cons_self ..)
    have hx : l.formPerm x ≠ x ↔ x ∈ l := by
      simpa using Set.ext_iff.mp (support_formPerm_of_nodup' l hl hl1) x
    have hσ : σ x = x ↔ l.formPerm x = x ∧ (p.map formPerm).prod x = x := by
      rw [← h.prod_map_formPerm, map_cons, prod_cons, hd.mul_apply_eq_iff]
    rw [flatten_cons, mem_append, ← hx, ← ih h.of_cons, Ne, hσ]
    tauto

/-- **Inverse in cycle notation:** reversing every cycle of a disjoint cycle notation for `σ` gives
one for `σ⁻¹`. -/
theorem inv (h : σ.IsCycleNotation p) :
    σ⁻¹.IsCycleNotation (p.map reverse) := by
  refine ⟨?_, forall_mem_map.mpr fun l hl ↦ by simpa using h.two_le_length l hl, ?_⟩
  · obtain ⟨hn, hd⟩ := List.nodup_flatten.mp h.nodup_flatten
    refine List.nodup_flatten.mpr
      ⟨forall_mem_map.mpr fun l hl ↦ nodup_reverse.mpr (hn l hl), ?_⟩
    rw [pairwise_map]
    exact hd.imp (disjoint_reverse_left.mpr <| disjoint_reverse_right.mpr ·)
  · rw [← h.prod_map_formPerm, prod_inv_reverse, map_map]
    refine ((reverse_perm _).prod_eq' ?_).symm.trans ?_
    · rw [pairwise_reverse, pairwise_map]
      exact (pairwise_map.mp h.pairwise_disjoint).imp fun hd ↦ by
        simpa [formPerm_reverse] using hd.symm.inv_left.inv_right.commute
    · simp [Function.comp_def, formPerm_reverse]

end IsCycleNotation

variable [Finite α] (σ : Perm α) in
/-- **Every permutation has a disjoint cycle notation.** -/
theorem exists_isCycleNotation : ∃ p : List (List α), σ.IsCycleNotation p := by
  cases nonempty_fintype α
  induction σ using cycle_induction_on with
  | base_one => exact ⟨[], isCycleNotation_nil_iff.mpr rfl⟩
  | base_cycles σ hσ =>
    obtain ⟨x, hx⟩ := hσ.nonempty_support
    refine ⟨[σ.toList x], by simpa using nodup_toList σ x, by simpa using hx, ?_⟩
    rw [map_singleton, prod_singleton, formPerm_toList, hσ.cycleOf_eq (mem_support.mp hx)]
  | induction_disjoint σ τ hd _ hσ hτ =>
    obtain ⟨p, hp⟩ := hσ
    obtain ⟨q, hq⟩ := hτ
    refine ⟨p ++ q, ?_, ?_, ?_⟩
    · rw [flatten_append, nodup_append]
      refine ⟨hp.nodup_flatten, hq.nodup_flatten, fun x hx y hy hxy ↦ ?_⟩
      subst hxy
      exact (hp.apply_ne_self_iff.mpr hx) <| (hd x).resolve_right (hq.apply_ne_self_iff.mpr hy)
    · simpa [or_imp, forall_and] using ⟨hp.two_le_length, hq.two_le_length⟩
    · rw [map_append, prod_append, hp.prod_map_formPerm, hq.prod_map_formPerm]

variable [Fintype α] {σ : Perm α} {p : List (List α)}

namespace IsCycleNotation

/-- The support of a permutation is the set of listed points. -/
theorem support_eq (h : σ.IsCycleNotation p) : σ.support = p.flatten.toFinset := by
  ext x
  rw [mem_support, h.apply_ne_self_iff, mem_toFinset]

/-- **The cycle type is read off a disjoint cycle notation:** it is the multiset of lengths of the
listed cycles. -/
theorem cycleType_eq (h : σ.IsCycleNotation p) : σ.cycleType = (p.map length : Multiset ℕ) := by
  rw [Equiv.Perm.cycleType_eq _ h.prod_map_formPerm
    (by simpa using fun l hl ↦ h.isCycle_formPerm hl) h.pairwise_disjoint, map_map]
  congr 1
  refine map_congr_left fun l hl ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, support_formPerm_of_nodup l (h.nodup hl)
    fun y hy ↦ by simpa [hy] using h.two_le_length l hl, toFinset_card_of_nodup (h.nodup hl)]

/-- The number of points moved by a permutation is the total length of the listed cycles. -/
theorem card_support (h : σ.IsCycleNotation p) : σ.support.card = (p.map length).sum := by
  rw [← sum_cycleType, h.cycleType_eq, Multiset.sum_coe]

/-- **The full cycle partition from a disjoint cycle notation:** the lengths of the listed cycles,
padded by one part equal to one for each point that is not listed. -/
theorem parts_partition_eq (h : σ.IsCycleNotation p) :
    σ.partition.parts = (p.map length : Multiset ℕ) +
      Multiset.replicate (Fintype.card α - (p.map length).sum) 1 := by
  rw [parts_partition, h.cycleType_eq, h.card_support]

end IsCycleNotation

end Equiv.Perm
