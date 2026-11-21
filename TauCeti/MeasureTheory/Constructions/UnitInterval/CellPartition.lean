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
of `x ↦ P.part (cellFin m x)`. Its parts are measurable, have positive volume `#A / m`, and are in
canonical bijection with the parts of `P`. Lifting preserves and reflects refinement, carries `⊤` to
`⊤`, and carries `⊥` to the partition into the `m` equal cells `ofFibers (cellFin m)`.

## Main definitions

* `Finpartition.cellPartition`: the partition of the unit interval induced by a partition of
  `Fin m`.
* `Finpartition.partsCellPartitionEquiv`: the bijection `P.parts ≃ P.cellPartition.parts` sending
  each vertex part to the union of its cells.

## Main results

* `Finpartition.mem_cellPartition_parts_iff`: the parts are the cell preimages of the parts of
  `P`.
* `Finpartition.coe_index_cellPartition`: the part through a point.
* `Finpartition.card_parts_cellPartition`: lifting preserves the number of parts.
* `Finpartition.volume_ne_zero_of_mem_cellPartition` and
  `Finpartition.volume_real_partsCellPartitionEquiv`: each lifted part has positive volume `#A / m`.
* `Finpartition.cellPartition_le_cellPartition_iff`, `Finpartition.cellPartition_top`, and
  `Finpartition.cellPartition_bot`: lifting is an order embedding compatible with `⊤` and `⊥`.
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

/-- The union of the cells over any part of `P` is a part of `P.cellPartition`. -/
theorem preimage_cellFin_mem_cellPartition {P : Finpartition (univ : Finset (Fin m))}
    {A : Finset (Fin m)} (hA : A ∈ P.parts) :
    cellFin m ⁻¹' (A : Set (Fin m)) ∈ P.cellPartition.parts :=
  P.mem_cellPartition_parts_iff.2 ⟨A, hA, rfl⟩

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

/-- The canonical bijection from the parts of `P` to the parts of `P.cellPartition`, sending each
part of `P` to the union of its cells in the unit interval. -/
noncomputable def partsCellPartitionEquiv (P : Finpartition (univ : Finset (Fin m))) :
    P.parts ≃ P.cellPartition.parts :=
  Equiv.ofBijective
    (fun A => ⟨cellFin m ⁻¹' (A.val : Set (Fin m)), P.preimage_cellFin_mem_cellPartition
        A.property⟩)
    ⟨fun _ _ h => Subtype.ext <| Finset.coe_injective <|
        cellFin_surjective.preimage_injective (Subtype.ext_iff.1 h),
      fun p => by
        obtain ⟨A, hA, hp⟩ := P.mem_cellPartition_parts_iff.1 p.property
        exact ⟨⟨A, hA⟩, Subtype.ext hp⟩⟩

/-- Each vertex part maps under `partsCellPartitionEquiv` to the union of its cells. -/
@[simp]
theorem partsCellPartitionEquiv_apply_coe (P : Finpartition (univ : Finset (Fin m)))
    (A : P.parts) :
    (P.partsCellPartitionEquiv A : Set I) = cellFin m ⁻¹' (A.val : Set (Fin m)) := by
  rw [partsCellPartitionEquiv]
  rfl

/-- The cell of `x` belongs to the vertex part corresponding to `p` if and only if `x ∈ p`. -/
@[simp]
theorem mem_partsCellPartitionEquiv_symm_iff (P : Finpartition (univ : Finset (Fin m)))
    (p : P.cellPartition.parts) (x : I) :
    cellFin m x ∈ (P.partsCellPartitionEquiv.symm p).val ↔ x ∈ (p : Set I) := by
  conv_rhs =>
    rw [← P.partsCellPartitionEquiv.apply_symm_apply p, partsCellPartitionEquiv_apply_coe]
  simp

/-- Under `partsCellPartitionEquiv.symm`, the part of `P.cellPartition` selected at `x` corresponds
to `P.part (cellFin m x)`. -/
@[simp]
theorem partsCellPartitionEquiv_symm_index (P : Finpartition (univ : Finset (Fin m))) (x : I) :
    P.partsCellPartitionEquiv.symm (P.cellPartition.indexedPartition.index x) =
      ⟨P.part (cellFin m x), P.part_mem.2 (mem_univ _)⟩ := by
  apply P.partsCellPartitionEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  simp

/-- Lifting a partition of `Fin m` to the unit interval preserves the number of parts. -/
@[simp]
theorem card_parts_cellPartition (P : Finpartition (univ : Finset (Fin m))) :
    #P.cellPartition.parts = #P.parts := by
  simpa only [Fintype.card_coe] using Fintype.card_congr P.partsCellPartitionEquiv.symm

/-- Every part of `P.cellPartition` has positive volume, since it contains at least one cell of
volume `1 / m`. -/
theorem volume_ne_zero_of_mem_cellPartition (P : Finpartition (univ : Finset (Fin m)))
    {s : Set I} (hs : s ∈ P.cellPartition.parts) : volume s ≠ 0 := by
  obtain ⟨A, hA, rfl⟩ := P.mem_cellPartition_parts_iff.1 hs
  obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hA
  refine ne_bot_of_le_ne_bot ?_
    (measure_mono (Set.preimage_mono (Set.singleton_subset_iff.2 hi)))
  rw [preimage_cellFin_singleton, volume_preimage_cellIdx i.isLt]
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m)

/-- The lifted part corresponding to `A : P.parts` has volume `#A.1 / m`. -/
theorem volume_real_partsCellPartitionEquiv (P : Finpartition (univ : Finset (Fin m)))
    (A : P.parts) :
    volume.real (P.partsCellPartitionEquiv A : Set I) = #A.val / m := by
  rw [partsCellPartitionEquiv_apply_coe, volume_real_preimage_cellFin]

/-- Lifting partitions of `Fin m` to the unit interval preserves and reflects refinement. -/
@[simp]
theorem cellPartition_le_cellPartition_iff {P Q : Finpartition (univ : Finset (Fin m))} :
    P.cellPartition ≤ Q.cellPartition ↔ P ≤ Q := by
  constructor
  · intro h A hA
    obtain ⟨t, ht, hsub⟩ := h (P.preimage_cellFin_mem_cellPartition hA)
    obtain ⟨B, hB, rfl⟩ := Q.mem_cellPartition_parts_iff.1 ht
    exact ⟨B, hB, Finset.coe_subset.1 (cellFin_surjective.preimage_subset_preimage_iff.1 hsub)⟩
  · intro h s hs
    obtain ⟨A, hA, rfl⟩ := P.mem_cellPartition_parts_iff.1 hs
    obtain ⟨B, hB, hAB⟩ := h hA
    exact ⟨_, Q.preimage_cellFin_mem_cellPartition hB,
      Set.preimage_mono (Finset.coe_subset.2 hAB)⟩

/-- Lifting partitions of `Fin m` to the unit interval is monotone. -/
@[gcongr]
theorem cellPartition_mono {P Q : Finpartition (univ : Finset (Fin m))} (h : P ≤ Q) :
    P.cellPartition ≤ Q.cellPartition :=
  cellPartition_le_cellPartition_iff.2 h

/-- Lifting partitions of `Fin m` to the unit interval is injective. -/
theorem cellPartition_injective :
    Function.Injective (cellPartition : Finpartition (univ : Finset (Fin m)) → _) :=
  fun _ _ h => le_antisymm (cellPartition_le_cellPartition_iff.1 h.le)
    (cellPartition_le_cellPartition_iff.1 h.ge)

/-- Two partitions of `Fin m` lift to the same cell partition if and only if they are equal. -/
@[simp]
theorem cellPartition_inj {P Q : Finpartition (univ : Finset (Fin m))} :
    P.cellPartition = Q.cellPartition ↔ P = Q :=
  cellPartition_injective.eq_iff

/-- The one-part partition of `Fin m` lifts to the one-part partition of the unit interval. -/
@[simp]
theorem cellPartition_top : (⊤ : Finpartition (univ : Finset (Fin m))).cellPartition = ⊤ := by
  refine eq_top_of_mem_parts ?_
  have htop : (univ : Finset (Fin m)) ∈ (⊤ : Finpartition (univ : Finset (Fin m))).parts := by
    classical
    rw [parts_top univ_nonempty.ne_empty]
    exact mem_singleton_self _
  simpa using preimage_cellFin_mem_cellPartition htop

/-- The singleton partition of `Fin m` lifts to the partition of the unit interval into its `m`
equal cells. -/
@[simp]
theorem cellPartition_bot :
    (⊥ : Finpartition (univ : Finset (Fin m))).cellPartition = ofFibers (cellFin m) := by
  ext s
  simp only [cellPartition, mem_ofFibers_parts, part_bot (mem_univ _)]
  refine exists_congr fun x => ?_
  have hpre : (fun z : I => ({cellFin m z} : Finset (Fin m))) ⁻¹' {{cellFin m x}} =
      cellFin m ⁻¹' {cellFin m x} := by
    ext z
    simp [Fin.ext_iff]
  rw [hpre]

end Finpartition
