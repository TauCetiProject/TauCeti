/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.UnitInterval
public import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# Partitions of the unit interval by groups of cells

A partition `P` of `Fin m` with `0 < m` lifts to the partition `P.cellPartition` of the unit
interval whose parts are the unions of the `m` equal cells over the parts of `P`, namely the fibres
of `x ↦ P.part (cellFin m x)`. Its parts are measurable and are exactly the cell preimages of the
parts of `P`, and the part selected at `x` by its canonical index is the cell preimage of the part
of `P` containing the cell of `x`.

## Main definitions

* `Finpartition.cellPartition`: the partition of the unit interval induced by a partition of
  `Fin m`.

## Main results

* `Finpartition.mem_cellPartition_parts_iff`: the parts are the cell preimages of the parts of
  `P`.
* `Finpartition.coe_index_cellPartition`: the part through a point.
-/

public section

open MeasureTheory TauCeti.unitInterval Finset
open scoped unitInterval

namespace Finpartition

variable {m : ℕ} [NeZero m]

/-- The partition of the unit interval obtained from a partition `P` of `Fin m` by grouping the
`m` equal cells of `I` according to the parts of `P`. -/
noncomputable def cellPartition (P : Finpartition (univ : Finset (Fin m))) :
    Finpartition (Set.univ : Set I) :=
  ofFibers fun x => P.part (cellFin m x)

/-- The part of `P` containing the cell of a point depends measurably on the point. -/
theorem measurable_part_cellFin (P : Finpartition (univ : Finset (Fin m))) :
    Measurable fun x : I => P.part (cellFin m x) :=
  (measurable_from_top (f := fun i : Fin m => P.part i)).comp measurable_cellFin

/-- The parts of `P.cellPartition` are measurable. -/
theorem measurableSet_of_mem_cellPartition (P : Finpartition (univ : Finset (Fin m))) :
    ∀ p ∈ P.cellPartition.parts, MeasurableSet p :=
  fun _ hp => measurableSet_of_mem_ofFibers P.measurable_part_cellFin hp

/-- The cells of the part of `P` containing the cell of `x` form the part of `P.cellPartition`
containing `x`. -/
theorem preimage_part_cellFin_mem (P : Finpartition (univ : Finset (Fin m))) (x : I) :
    cellFin m ⁻¹' (P.part (cellFin m x) : Set (Fin m)) ∈ P.cellPartition.parts := by
  refine mem_ofFibers_parts.2 ⟨x, Set.ext fun z => ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
  exact (P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).symm

/-- The parts of `P.cellPartition` are exactly the unions of the cells over the parts of `P`. -/
theorem mem_cellPartition_parts_iff (P : Finpartition (univ : Finset (Fin m))) {s : Set I} :
    s ∈ P.cellPartition.parts ↔ ∃ A ∈ P.parts, cellFin m ⁻¹' (A : Set (Fin m)) = s := by
  constructor
  · intro hs
    obtain ⟨x, rfl⟩ := mem_ofFibers_parts.1 hs
    refine ⟨P.part (cellFin m x), P.part_mem.2 (mem_univ _), Set.ext fun z => ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
    exact P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hA
    obtain ⟨x, rfl⟩ := cellFin_surjective i
    rw [← P.part_eq_of_mem hA hi]
    exact P.preimage_part_cellFin_mem x

/-- **The part through a point.** The part of `P.cellPartition` that its canonical index selects at
`x` is the union of the cells over the part of `P` containing the cell of `x`. -/
@[simp]
theorem coe_index_cellPartition (P : Finpartition (univ : Finset (Fin m))) (x : I) :
    (P.cellPartition.indexedPartition.index x : Set I) =
      cellFin m ⁻¹' (P.part (cellFin m x) : Set (Fin m)) := by
  -- `x` lies in the part through it, so the canonical index selects that part.
  have hx : x ∈ ((⟨_, P.preimage_part_cellFin_mem x⟩ : P.cellPartition.parts) : Set I) :=
    P.mem_part (mem_univ _)
  exact congrArg Subtype.val (P.cellPartition.indexedPartition.mem_iff_index_eq.1 hx)

end Finpartition
