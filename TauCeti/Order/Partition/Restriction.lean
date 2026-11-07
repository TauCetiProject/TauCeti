/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Equipartition
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Retaining cells when restricting a finite partition

Restricting a partition intersects its cells with the retained vertex set and discards empty
intersections. If every cell survives, intersection gives a bijection between the old and new
cells. For an equipartition, deleting fewer vertices than the floor mean cell size guarantees
this survival. More quantitatively, deleting at most an `η`-fraction of the floor mean size,
with `0 ≤ η < 1`, leaves at least a `1 - η` fraction of every cell.

These statements provide cell matchings and retention estimates when auxiliary vertices are
removed from a divisible padded host. They do not assert that the restricted partition is
equitable: surviving cells may have different losses and must subsequently be rebalanced.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding-and-rebalancing setting.
-/

public section

open Finset

namespace Finpartition

variable {V : Type*} [DecidableEq V] {s t : Finset V} (P : Finpartition s)

/-- If every cell meets the retained set, intersection with that set bijects the original
cells with the cells of the restricted partition. No equitability is required. -/
theorem exists_partsEquiv_restrict (ht : t ⊆ s)
    (hret : ∀ A ∈ P.parts, (A ∩ t).Nonempty) :
    ∃ e : P.parts ≃ (P.restrict ht).parts, ∀ A, (e A).val = A.val ∩ t := by
  let f (A : P.parts) : (P.restrict ht).parts :=
    ⟨A.val ∩ t, by
      rw [parts_restrict, mem_erase, mem_image]
      exact ⟨(hret A.val A.property).ne_empty,
        A.val, A.property, by simp [inter_comm]⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro A B h
      obtain ⟨v, hv⟩ := hret A.val A.property
      obtain ⟨hvA, hvt⟩ := mem_inter.1 hv
      have hvB : v ∈ B.val := by
        have hsets : A.val ∩ t = B.val ∩ t := congrArg Subtype.val h
        exact (mem_inter.1 (hsets ▸ mem_inter.2 ⟨hvA, hvt⟩)).1
      exact Subtype.ext (P.eq_of_mem_parts A.property B.property hvA hvB)
    · intro B
      have hB : B.val ∈ (P.parts.image (fun A ↦ A ∩ t)).erase ∅ := by
        simpa only [parts_restrict, Finset.bot_eq_empty] using B.property
      obtain ⟨A, hA, hAB⟩ := mem_image.1 (mem_erase.1 hB).2
      exact ⟨⟨A, hA⟩, Subtype.ext (by simpa [f, inter_comm] using hAB)⟩
  exact ⟨Equiv.ofBijective f hf, fun _ ↦ rfl⟩

/-- Deleting fewer vertices than the size of every original cell preserves all cells.
The resulting matching is intersection with the retained set. -/
theorem exists_partsEquiv_restrict_of_card_sdiff_lt (ht : t ⊆ s)
    (hsmall : ∀ A ∈ P.parts, #(s \ t) < #A) :
    ∃ e : P.parts ≃ (P.restrict ht).parts, ∀ A, (e A).val = A.val ∩ t := by
  apply P.exists_partsEquiv_restrict ht
  intro A hA
  by_contra h
  have hsub : A ⊆ s \ t := by
    intro v hv
    exact mem_sdiff.2 ⟨P.le hA hv, fun hvt ↦ h ⟨v, mem_inter.2 ⟨hv, hvt⟩⟩⟩
  exact (hsmall A hA).not_ge (card_le_card hsub)

variable {P}

/-- An equipartition loses no cells when fewer than the floor mean cell size vertices are
deleted. The restricted partition need not itself be equitable. -/
theorem IsEquipartition.card_parts_restrict_eq (hP : P.IsEquipartition) (ht : t ⊆ s)
    (hsmall : #(s \ t) < #s / #P.parts) :
    #(P.restrict ht).parts = #P.parts := by
  obtain ⟨e, _⟩ := P.exists_partsEquiv_restrict_of_card_sdiff_lt ht
    (fun A hA ↦ hsmall.trans_le (hP.average_le_card_part hA))
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

/-- Deleting at most an `η`-fraction of the floor mean cell size of a nonempty equipartition,
where `0 ≤ η < 1`, retains at least a `1 - η` fraction of each cell and preserves the cell
index set. The matching explicitly identifies every new cell as the trace of its old cell. -/
theorem IsEquipartition.exists_partsEquiv_restrict (hP : P.IsEquipartition)
    (hs : s.Nonempty) (ht : t ⊆ s) {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1)
    (hloss : (#(s \ t) : ℝ) ≤ η * (#s / #P.parts : ℕ)) :
    ∃ e : P.parts ≃ (P.restrict ht).parts, ∀ A,
      (e A).val = A.val ∩ t ∧ (1 - η) * (#A.val : ℝ) ≤ #(e A).val := by
  have havg : 0 < #s / #P.parts :=
    Nat.div_pos (P.card_parts_le_card) (card_pos.2 (P.parts_nonempty hs.ne_empty))
  have hsmall : #(s \ t) < #s / #P.parts := by
    have hpos : (0 : ℝ) < (#s / #P.parts : ℕ) := by exact_mod_cast havg
    have : (#(s \ t) : ℝ) < (#s / #P.parts : ℕ) := by nlinarith
    exact_mod_cast this
  obtain ⟨e, he⟩ := P.exists_partsEquiv_restrict_of_card_sdiff_lt ht
    (fun A hA ↦ hsmall.trans_le (hP.average_le_card_part hA))
  refine ⟨e, fun A ↦ ⟨he A, ?_⟩⟩
  have hsub : A.val \ t ⊆ s \ t := Finset.sdiff_subset_sdiff_left t (P.le A.property)
  have hcount : (#A.val : ℝ) ≤ #(s \ t) + #(A.val ∩ t) := by
    have hcard := card_sdiff_add_card_inter A.val t
    have hle := card_le_card hsub
    exact_mod_cast (by omega : #A.val ≤ #(s \ t) + #(A.val ∩ t))
  have havgA : ((#s / #P.parts : ℕ) : ℝ) ≤ #A.val := by
    exact_mod_cast hP.average_le_card_part A.property
  rw [he A]
  nlinarith

end Finpartition
