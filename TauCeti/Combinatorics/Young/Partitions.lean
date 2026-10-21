/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.Combinatorics.Young.Diagram

/-!
# Partitions and Young diagrams

Mathlib relates partitions of `n` and Young diagrams with `n` cells by
`YoungDiagram.ofPartition`, which builds the Young diagram whose rows are the decreasingly sorted
parts of a partition, and `YoungDiagram.toPartition`, which reads the row lengths of a sized
diagram back as a partition; these are inverse to each other (`YoungDiagram.equivPartition`).

This file adds the individual row lengths and the first-column length of
`YoungDiagram.ofPartition`, row- and column-length bounds for the special shapes
`Nat.Partition.ones`, `Nat.Partition.indiscrete` and `Nat.Partition.singletonSecondRow`, the parts
of `YoungDiagram.toPartition`, the injectivity of `YoungDiagram.ofPartition`, and the
**shape partition** `TauCeti.shapePartition` of a Young diagram, a partition of `μ.card` itself
rather than of a number equal to it.

## References

* [Mathlib PR #39722](https://github.com/leanprover-community/mathlib4/pull/39722)
  (Kevin Gomez), which added `Mathlib/Combinatorics/Enumerative/Partition/YoungDiagram.lean`:
  the `YoungDiagram.ofPartition`/`YoungDiagram.toPartition` correspondence,
  `YoungDiagram.equivPartition` and `Nat.Partition.conjugate` that this file builds on.
-/

public section

namespace YoungDiagram

/-- The parts of the partition of a sized Young diagram are its row lengths. -/
@[simp]
theorem toPartition_parts {n : ℕ} (μ : YoungDiagram) (h : μ.card = n) :
    (μ.toPartition h).parts = μ.rowLens := by
  rfl

/-- The row lengths of the Young diagram of a partition are its decreasingly sorted parts, padded
by zeros. -/
@[simp]
theorem rowLen_ofPartition {n : ℕ} (ν : n.Partition) (i : ℕ) :
    (ofPartition ν).rowLen i = (ν.parts.sort (· ≥ ·)).getD i 0 := by
  rw [← getD_rowLens, rowLens_ofPartition_eq_sort_parts]

/-- **The Young diagram of a partition has one row per part**: its rows are the parts, so the
length of its first column counts them. -/
@[simp]
theorem colLen_zero_ofPartition {n : ℕ} (ν : n.Partition) :
    (ofPartition ν).colLen 0 = ν.parts.card := by
  rw [← length_rowLens, rowLens_ofPartition_eq_sort_parts, Multiset.length_sort]

/-- The Young diagram construction is injective on partitions of a fixed size. -/
theorem ofPartition_injective {n : ℕ} : Function.Injective (ofPartition (n := n)) :=
  fun _ _ h => equivPartition.symm.injective (Subtype.ext h)

/-- **The Young diagram of the partition `(1ⁿ)` is a single column**: every part is `1`, so every
row has at most one cell. -/
theorem rowLen_ofPartition_ones_le_one (n i : ℕ) :
    (ofPartition (TauCeti.Nat.Partition.ones n)).rowLen i ≤ 1 := by
  rw [rowLen_ofPartition, TauCeti.Nat.Partition.ones_parts]
  rcases lt_or_ge i ((Multiset.replicate n 1).sort (· ≥ ·)).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact le_of_eq (Multiset.eq_of_mem_replicate
      ((Multiset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi)))
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.zero_le 1

/-- **The Young diagram of the partition `(n)` has at most one row**: for `n > 0` its only part is
`n`, so there is nothing below the first row, and for `n = 0` the diagram is empty. -/
theorem colLen_ofPartition_indiscrete_le_one (n : ℕ) :
    (ofPartition (Nat.Partition.indiscrete n)).colLen 0 ≤ 1 := by
  rw [colLen_zero_ofPartition]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.Partition.indiscrete_parts hn.ne']
    simp

/-- The second row of the Young diagram of the partition `(n+1, 1)` is a single cell. -/
theorem rowLen_ofPartition_singletonSecondRow_one (n : ℕ) :
    (ofPartition (TauCeti.Nat.Partition.singletonSecondRow n)).rowLen 1 = 1 := by
  rw [rowLen_ofPartition, TauCeti.Nat.Partition.sort_parts_singletonSecondRow]
  rfl

/-- The Young diagram of the partition `(n+1, 1)` has no third row. -/
theorem rowLen_ofPartition_singletonSecondRow_two (n : ℕ) :
    (ofPartition (TauCeti.Nat.Partition.singletonSecondRow n)).rowLen 2 = 0 := by
  rw [rowLen_ofPartition, TauCeti.Nat.Partition.sort_parts_singletonSecondRow]
  rfl

end YoungDiagram

namespace TauCeti

/-- The **shape partition** of a Young diagram: the partition of `μ.card` whose parts are the row
lengths. -/
def shapePartition (μ : YoungDiagram) : μ.card.Partition :=
  μ.toPartition rfl

/-- A partition built from a Young diagram along the trivial equality of sizes is its shape
partition. -/
@[simp]
theorem toPartition_eq_shapePartition (μ : YoungDiagram) : μ.toPartition rfl = shapePartition μ :=
  (rfl)

/-- The Young diagram of the shape partition of a Young diagram is that diagram. -/
@[simp]
theorem ofPartition_shapePartition (μ : YoungDiagram) :
    YoungDiagram.ofPartition (shapePartition μ) = μ :=
  YoungDiagram.ofPartition_toPartition rfl

/-- The parts of the shape partition are the row lengths of the diagram. -/
@[simp]
theorem shapePartition_parts (μ : YoungDiagram) :
    (shapePartition μ).parts = μ.rowLens := by
  rfl

/-- Sorting the parts of the shape partition into decreasing order returns the row lengths, which
are already decreasing.  This is not a `simp` lemma: `simp` reaches the same normal form through
`TauCeti.shapePartition_parts` and `YoungDiagram.sort_coe_rowLens`. -/
theorem shapePartition_parts_sort (μ : YoungDiagram) :
    (shapePartition μ).parts.sort (· ≥ ·) = μ.rowLens := by
  rw [shapePartition_parts, YoungDiagram.sort_coe_rowLens]

end TauCeti
