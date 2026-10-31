/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Dominance
public import TauCeti.Combinatorics.Young.Partitions

/-!
# Conjugate partitions and dominance

Mathlib defines the conjugate `Nat.Partition.conjugate` of a natural-number partition by
transposing its Young diagram, and proves that conjugation is an involution
(`Nat.Partition.conjugate_conjugate`).  This file records the parts and the Young diagram of the
conjugate, and proves that conjugation reverses the dominance order. The parts of the conjugate
are the column lengths of the original partition: `Nat.Partition.sum_map_conjugate_parts` turns a
sum over them into a sum over columns, where column `k` counts the parts larger than `k`.
Consequently dominance can be read off column by column: `μ` dominates `ν` exactly when, for every
`k`, the first `k` columns of the Young diagram of `μ` hold at most as many boxes as those of `ν`
(`Nat.Partition.dominates_iff_forall_sum_map_min_le`).

The reversal theorem supplies the order duality behind the row/column symmetry of Specht
modules and permutation modules.

The Young diagrams of the two extreme partitions, which the duality exchanges, are recorded
with the partition–diagram correspondence in `TauCeti/Combinatorics/Young/Partitions.lean`
(`YoungDiagram.rowLen_ofPartition_ones_le_one` and
`YoungDiagram.colLen_ofPartition_indiscrete_le_one`).

## References

* W. Fulton, *Young Tableaux*, London Mathematical Society Student Texts 35, §1.1.
* [Mathlib PR #42725](https://github.com/leanprover-community/mathlib4/pull/42725)
  (Kim Morrison) — the draft upstream adaptation of the dominance material; the dot-notation
  `Dominates.conjugate` and the name and orientation of `conjugate_dominates_conjugate_iff`
  follow the form prepared for that PR.
-/

public section

namespace TauCeti

open scoped BigOperators

private theorem sum_map_min_rowLens_eq_card_filter_snd (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.map (min k)).sum = (μ.cells.filter fun c => c.2 < k).card := by
  rw [YoungDiagram.rowLens, List.map_map,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  symm
  calc
    (μ.cells.filter fun c => c.2 < k).card =
        ∑ i ∈ Finset.range (μ.colLen 0),
          ((μ.cells.filter fun c => c.2 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
      rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen]
      exact μ.up_left_mem (by rfl) c.2.zero_le hc.1
    _ = ∑ i ∈ Finset.range (μ.colLen 0), min k (μ.rowLen i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hfiber :
          (μ.cells.filter fun c => c.2 < k).filter (fun c => c.1 = i) =
            {i} ×ˢ Finset.range (min k (μ.rowLen i)) := by
        ext c
        simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_range, lt_min_iff]
        rw [YoungDiagram.mem_iff_lt_rowLen]
        aesop
      rw [hfiber, Finset.card_product]
      simp

private theorem card_filter_fst_transpose (μ : YoungDiagram) (k : ℕ) :
    (μ.transpose.cells.filter fun c => c.1 < k).card = (μ.cells.filter fun c => c.2 < k).card := by
  apply Finset.card_equiv (Equiv.prodComm ℕ ℕ)
  intro c
  simp

private theorem sum_take_transpose_rowLens (μ : YoungDiagram) (k : ℕ) :
    (μ.transpose.rowLens.take k).sum = (μ.rowLens.map (min k)).sum := by
  rw [YoungDiagram.sum_take_rowLens_eq_card_filter_fst, card_filter_fst_transpose,
    sum_map_min_rowLens_eq_card_filter_snd]

private theorem sum_sub_add_mul_length_takeWhile {l : List ℕ} (hl : l.SortedGE) (k : ℕ) :
    (l.map fun x => x - k).sum +
        k * (l.takeWhile fun x => decide (k < x)).length =
      (l.takeWhile fun x => decide (k < x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hlsorted : l.SortedGE := hl.pairwise.tail.sortedGE
      by_cases ha : k < a
      · rw [List.takeWhile_cons_of_pos (by simpa using ha)]
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have htail := ih hlsorted
        rw [Nat.mul_succ]
        omega
      · have hale : a ≤ k := Nat.le_of_not_gt ha
        have htail : ∀ x ∈ l, x ≤ k := by
          intro x hx
          exact (hl.pairwise.rel_head_tail (by simpa using hx)).trans hale
        have hsum : (l.map fun x => x - k).sum = 0 := by
          apply List.sum_eq_zero
          intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          exact Nat.sub_eq_zero_of_le (htail x hx)
        rw [List.takeWhile_cons_of_neg (by simpa using ha)]
        simp only [List.map_cons, List.sum_cons, List.sum_nil, List.length_nil, mul_zero,
          add_zero, Nat.sub_eq_zero_of_le hale]
        simpa only [zero_add] using hsum

private theorem sum_take_le_mul_add_sum_sub (l : List ℕ) (k r : ℕ) :
    (l.take r).sum ≤ k * r + (l.map fun x => x - k).sum := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
      cases l with
      | nil => simp
      | cons a l =>
          simp only [List.take_succ_cons, List.sum_cons, List.map_cons, Nat.mul_succ]
          have htail := ih l
          omega

private theorem sum_min_add_sum_sub (l : List ℕ) (k : ℕ) :
    (l.map (min k)).sum + (l.map fun x => x - k).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      omega

private theorem sum_map_min_le_of_prefix_sum_le {l₁ l₂ : List ℕ}
    (hl₂ : l₂.SortedGE) (hsum : l₁.sum = l₂.sum)
    (hle : ∀ r, (l₂.take r).sum ≤ (l₁.take r).sum) (k : ℕ) :
    (l₁.map (min k)).sum ≤ (l₂.map (min k)).sum := by
  let r := (l₂.takeWhile fun x => decide (k < x)).length
  have htake :
      l₂.take r = l₂.takeWhile fun x => decide (k < x) := by
    dsimp only [r]
    calc
      l₂.take (l₂.takeWhile fun x => decide (k < x)).length =
          ((l₂.takeWhile fun x => decide (k < x)) ++
            l₂.dropWhile fun x => decide (k < x)).take
              (l₂.takeWhile fun x => decide (k < x)).length := by
        rw [l₂.takeWhile_append_dropWhile]
      _ = l₂.takeWhile fun x => decide (k < x) := List.take_left
  have hexcess :
      (l₂.map fun x => x - k).sum + k * r = (l₂.take r).sum := by
    rw [htake]
    exact sum_sub_add_mul_length_takeWhile hl₂ k
  have hsub :
      (l₂.map fun x => x - k).sum ≤ (l₁.map fun x => x - k).sum := by
    have hpref := hle r
    have hupper := sum_take_le_mul_add_sum_sub l₁ k r
    omega
  have hsplit₁ := sum_min_add_sum_sub l₁ k
  have hsplit₂ := sum_min_add_sum_sub l₂ k
  omega

end TauCeti

/-- The Young diagram of the conjugate partition is the transposed Young diagram. -/
@[simp]
theorem YoungDiagram.ofPartition_conjugate {n : ℕ} (μ : n.Partition) :
    YoungDiagram.ofPartition μ.conjugate = (YoungDiagram.ofPartition μ).transpose := by
  rw [Nat.Partition.conjugate]
  exact YoungDiagram.ofPartition_toPartition _

namespace Nat.Partition

/-- The parts of the conjugate partition are the row lengths of the transposed diagram. -/
@[simp]
theorem conjugate_parts {n : ℕ} (μ : n.Partition) :
    μ.conjugate.parts = ((YoungDiagram.ofPartition μ).transpose.rowLens : Multiset ℕ) := by
  rw [Nat.Partition.conjugate]
  exact YoungDiagram.toPartition_parts _ _

-- Not `@[simp]`: with `conjugate_parts` in the default simp set the left-hand side is no
-- longer in simp normal form (the parts reduce to the transposed row lengths before sorting).
/-- The decreasing parts of the conjugate partition are the row lengths of the transposed
diagram. -/
theorem conjugate_parts_sort {n : ℕ} (μ : n.Partition) :
    μ.conjugate.parts.sort (· ≥ ·) = (YoungDiagram.ofPartition μ).transpose.rowLens := by
  rw [← YoungDiagram.rowLens_ofPartition_eq_sort_parts μ.conjugate,
    YoungDiagram.ofPartition_conjugate]

/-- **The parts of the conjugate partition are the column lengths.** A sum over the parts of the
conjugate of `μ` is the sum over columns `k`, where column `k` has one cell for each part of `μ`
larger than `k`. The range of columns may be any bound on the parts of `μ`; the empty columns
beyond the largest part contribute `g 0 = 0`. -/
theorem sum_map_conjugate_parts {M : Type*} [AddCommMonoid M] {n : ℕ} (μ : n.Partition)
    (g : ℕ → M) (hg : g 0 = 0) {m : ℕ} (hm : ∀ i ∈ μ.parts, i ≤ m) :
    (μ.conjugate.parts.map g).sum =
      ∑ k ∈ Finset.range m, g (μ.parts.filter (k < ·)).card := by
  set D := YoungDiagram.ofPartition μ
  -- A column beyond the bound `m` is empty, so the first row has length at most `m`.
  have hcol (k : ℕ) : (0 < D.colLen k) ↔ k < D.rowLen 0 := by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  have hrow : D.rowLen 0 ≤ m := by
    by_contra! h
    have hpos := (hcol m).mpr h
    rw [YoungDiagram.colLen_ofPartition, Multiset.card_pos_iff_exists_mem] at hpos
    obtain ⟨i, hi⟩ := hpos
    rw [Multiset.mem_filter] at hi
    exact (hm i hi.1).not_gt hi.2
  rw [conjugate_parts, YoungDiagram.sum_map_coe_rowLens, YoungDiagram.colLen_transpose]
  simp only [YoungDiagram.rowLen_transpose, ← YoungDiagram.colLen_ofPartition]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hrow) fun k _ hk => ?_
  rw [Finset.mem_range, ← hcol, not_lt, Nat.le_zero] at hk
  rw [hk, hg]

/-- **Conjugation of partitions reverses dominance.** If `μ` dominates `ν`, then the conjugate
of `ν` dominates the conjugate of `μ`. -/
protected theorem Dominates.conjugate {n : ℕ} {μ ν : n.Partition} (h : μ.Dominates ν) :
    ν.conjugate.Dominates μ.conjugate := by
  rw [dominates_iff]
  intro k
  rw [conjugate_parts_sort, conjugate_parts_sort,
    TauCeti.sum_take_transpose_rowLens, TauCeti.sum_take_transpose_rowLens,
    YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    YoungDiagram.rowLens_ofPartition_eq_sort_parts]
  apply TauCeti.sum_map_min_le_of_prefix_sum_le
  · exact (Multiset.pairwise_sort ν.parts (· ≥ ·)).sortedGE
  · rw [sum_sort_parts, sum_sort_parts]
  · exact dominates_iff.mp h

/-- Conjugation of partitions reverses dominance: the conjugate of `μ` dominates the conjugate
of `ν` exactly when `ν` dominates `μ`. -/
@[simp]
theorem conjugate_dominates_conjugate_iff {n : ℕ} {μ ν : n.Partition} :
    μ.conjugate.Dominates ν.conjugate ↔ ν.Dominates μ :=
  ⟨fun h => by simpa using h.conjugate, fun h => h.conjugate⟩

/-- Dominance compared column by column: `μ` dominates `ν` exactly when, for every `k`, the first
`k` columns of the Young diagram of `μ` hold at most as many boxes as those of `ν`. These boxes
number `∑ᵢ min k λᵢ` over the parts `λᵢ`. For the Jordan type of a nilpotent endomorphism this
sum is the dimension of the kernel of its `k`-th power. -/
theorem dominates_iff_forall_sum_map_min_le {n : ℕ} {μ ν : n.Partition} :
    μ.Dominates ν ↔ ∀ k, (μ.parts.map (min k)).sum ≤ (ν.parts.map (min k)).sum := by
  have hsort (ξ : n.Partition) (k : ℕ) :
      ((ξ.parts.sort (· ≥ ·)).map (min k)).sum = (ξ.parts.map (min k)).sum := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq]
  rw [← conjugate_dominates_conjugate_iff, dominates_iff]
  refine forall_congr' fun k => ?_
  rw [conjugate_parts_sort, conjugate_parts_sort, TauCeti.sum_take_transpose_rowLens,
    TauCeti.sum_take_transpose_rowLens, YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    YoungDiagram.rowLens_ofPartition_eq_sort_parts, hsort, hsort]

end Nat.Partition
