/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# Composing relative CW complexes

Let `C` be a CW complex relative to `D`, and let `D` in turn be a CW complex relative to `E`, in a
Hausdorff space. Then `C` is a CW complex relative to `E` (`TauCeti.relCWComplexTrans`), whose
`n`-cells are the `n`-cells of `D` together with the `n`-cells of `C`, with their characteristic
maps (`TauCeti.relCWComplexTransCellEquiv`). Taking `E = ∅` and passing to an absolute CW complex
with `Topology.RelCWComplex.toCWComplex`, a complex built by attaching cells to a CW complex is a
CW complex.

One compatibility condition between the two structures is needed. The boundary of an `n`-cell of
`C` must lie in finitely many cells of dimension less than `n`, so the part of it in `D` must lie
in the skeleton `skeletonLT D n`. This is the only hypothesis. It holds, for instance, when all
cells of `D` have dimension less than all cells of `C`, the situation of a tower of cell
attachments of increasing dimension. Without it the cells of `D` and of `C` together need not
satisfy the closure-finiteness axiom: attaching a `1`-cell to the closed `2`-disk, with its usual
cells, along two interior points of the disk gives a CW complex relative to the disk, but the
boundary of the `1`-cell lies in the open `2`-cell.

Given the condition, the boundary of a cell of `C` is compact, so it meets only finitely many open
cells of `D` (`TauCeti.finite_setOf_nonempty_inter_openCell_of_isCompact`); those of them that
meet the boundary have dimension less than `n`. The weak topology of the composite combines the
weak topologies of the two structures, because every closed cell of `D` lies in `D`.

## Main definitions

* `TauCeti.relCWComplexTrans`: the CW structure on `C` relative to `E`.
* `TauCeti.relCWComplexTransCellEquiv`: its `n`-cells are the `n`-cells of `D` and of `C`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 for CW complexes built by attaching cells inductively, and the Appendix,
  Proposition A.1, for the compactness argument.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D E : Set X} [RelCWComplex C D]
  [RelCWComplex D E]

/-- The boundary of an `n`-cell of `C` lies in `E` together with finitely many closed cells of `D`
of dimension less than `n` and finitely many closed cells of `C` of dimension less than `n`, as
soon as its part in `D` lies in the skeleton `skeletonLT D n`. -/
private lemma exists_mapsTo_sphere_trans {n : ℕ} (i : cell C n)
    (h : cellFrontier n i ∩ D ⊆ skeletonLT D n) :
    ∃ I : Π m, Finset (cell D m ⊕ cell C m), MapsTo (map n i) (sphere 0 1)
      (E ∪ ⋃ (m < n) (j ∈ I m), Sum.elim (fun j ↦ closedCell m j) (fun j ↦ closedCell m j) j) := by
  classical
  obtain ⟨J, hJ⟩ := RelCWComplex.mapsTo n i
  have hK : IsCompact (cellFrontier n i ∩ D) := isCompact_cellFrontier.inter_right (isClosedBase C)
  have hS := finite_setOf_nonempty_inter_openCell_of_isCompact (C := D) hK
  let S (m : ℕ) : Finset (cell D m) :=
    (hS.preimage (sigma_mk_injective.injOn (s := (Sigma.mk m) ⁻¹' _))).toFinset
  refine ⟨fun m ↦ (S m).map .inl ∪ (J m).map .inr, fun x hx ↦ ?_⟩
  have hxi : map n i x ∈ cellFrontier n i := mem_image_of_mem _ hx
  rcases hJ hx with hxD | hxJ
  · rcases mem_skeletonLT_iff.1 (h ⟨hxi, hxD⟩) with hxE | ⟨m, hmn, j, hxj⟩
    · exact Or.inl hxE
    refine Or.inr (mem_iUnion₂_of_mem (by exact_mod_cast hmn) (mem_iUnion₂_of_mem
      (Finset.mem_union_left _ (Finset.mem_map_of_mem _ ?_)) (openCell_subset_closedCell m j hxj)))
    exact (Set.Finite.mem_toFinset _).2 ⟨map n i x, ⟨hxi, hxD⟩, hxj⟩
  · obtain ⟨m, hmn, hxJ⟩ := mem_iUnion₂.1 hxJ
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hxJ
    exact Or.inr (mem_iUnion₂_of_mem hmn (mem_iUnion₂_of_mem
      (Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)) hxj))

variable (C D E) in
/-- **Composing relative CW complexes.** If `C` is a CW complex relative to `D`, and `D` is a CW
complex relative to `E`, then `C` is a CW complex relative to `E`, as soon as the part in `D` of
the boundary of each `n`-cell of `C` lies in the skeleton `skeletonLT D n`. Its `n`-cells are the
`n`-cells of `D` together with those of `C`, with the same characteristic maps.

The structure is not an instance: the base of a relative CW complex is an `outParam`, so `C`
cannot carry one instance for each base. -/
@[instance_reducible]
def relCWComplexTrans (h : ∀ n (i : cell C n), cellFrontier n i ∩ D ⊆ skeletonLT D n) :
    RelCWComplex C E where
  cell n := cell D n ⊕ cell C n
  map n := Sum.elim (map n) (map n)
  source_eq n i := by cases i <;> exact source_eq n _
  continuousOn n i := by cases i <;> exact RelCWComplex.continuousOn n _
  continuousOn_symm n i := by cases i <;> exact continuousOn_symm n _
  pairwiseDisjoint' := by
    rintro ⟨n, i | i⟩ - ⟨m, j | j⟩ - hne
    · exact disjoint_openCell_of_ne (by rintro ⟨⟩; exact hne rfl)
    · exact (disjointBase m j).symm.mono_left (openCell_subset_complex n i)
    · exact (disjointBase n i).mono_right (openCell_subset_complex m j)
    · exact disjoint_openCell_of_ne (by rintro ⟨⟩; exact hne rfl)
  disjointBase' n i := by
    rcases i with i | i
    · exact disjointBase n i
    · exact (disjointBase n i).mono_right (base_subset_complex (C := D))
  mapsTo n i := by
    classical
    rcases i with i | i
    · obtain ⟨J, hJ⟩ := RelCWComplex.mapsTo n i
      refine ⟨fun m ↦ (J m).map .inl, hJ.mono_right (union_subset_union_right _ ?_)⟩
      refine iUnion₂_mono fun m _ ↦ iUnion₂_subset fun j hj ↦ ?_
      exact subset_iUnion₂_of_subset (Sum.inl j) (Finset.mem_map_of_mem _ hj) subset_rfl
    · obtain ⟨I, hI⟩ := exists_mapsTo_sphere_trans i (h n i)
      refine ⟨I, hI.mono_right (union_subset_union_right _ ?_)⟩
      refine iUnion₂_mono fun m _ ↦ iUnion₂_mono fun j _ ↦ ?_
      rcases j with j | j <;> exact subset_rfl
  closed' A hAC hA := by
    refine (RelCWComplex.closed C A hAC).2 ⟨fun n j ↦ hA.1 n (.inr j), ?_⟩
    refine (RelCWComplex.closed D (A ∩ D) inter_subset_right).2 ⟨fun n j ↦ ?_, ?_⟩
    · rw [inter_assoc, inter_eq_right.2 (closedCell_subset_complex n j)]
      exact hA.1 n (.inl j)
    · rw [inter_assoc, inter_eq_right.2 (base_subset_complex (C := D))]
      exact hA.2
  isClosedBase := isClosedBase D
  union' := by
    simp_rw [iUnion_sum, Sum.elim_inl, Sum.elim_inr, iUnion_union_distrib, ← union_assoc]
    exact (congrArg (· ∪ _) (RelCWComplex.union (C := D))).trans (RelCWComplex.union (C := C))

variable (h : ∀ n (i : cell C n), cellFrontier n i ∩ D ⊆ skeletonLT D n)

/-- The `n`-cells of `C` relative to `E` are the `n`-cells of `D` together with the `n`-cells of
`C`. -/
def relCWComplexTransCellEquiv (n : ℕ) :
    @cell X _ C E (relCWComplexTrans C D E h) n ≃ cell D n ⊕ cell C n :=
  Equiv.refl _

/-- The characteristic map of a cell of `D`, as a cell of `C` relative to `E`, is its
characteristic map in `D`. -/
@[simp]
lemma map_relCWComplexTrans_inl (n : ℕ) (i : cell D n) :
    @map X _ C E (relCWComplexTrans C D E h) n ((relCWComplexTransCellEquiv h n).symm (.inl i)) =
      map n i :=
  (rfl)

/-- The characteristic map of a cell of `C`, as a cell of `C` relative to `E`, is its
characteristic map relative to `D`. -/
@[simp]
lemma map_relCWComplexTrans_inr (n : ℕ) (i : cell C n) :
    @map X _ C E (relCWComplexTrans C D E h) n ((relCWComplexTransCellEquiv h n).symm (.inr i)) =
      map n i :=
  (rfl)

/-- The open cells of `C` relative to `E` coming from `D` are the open cells of `D`. -/
@[simp]
lemma openCell_relCWComplexTrans_inl (n : ℕ) (i : cell D n) :
    @openCell X _ C E (relCWComplexTrans C D E h) n
      ((relCWComplexTransCellEquiv h n).symm (.inl i)) = openCell n i :=
  (rfl)

/-- The open cells of `C` relative to `E` coming from `C` are the open cells of `C` relative to
`D`. -/
@[simp]
lemma openCell_relCWComplexTrans_inr (n : ℕ) (i : cell C n) :
    @openCell X _ C E (relCWComplexTrans C D E h) n
      ((relCWComplexTransCellEquiv h n).symm (.inr i)) = openCell n i :=
  (rfl)

/-- The closed cells of `C` relative to `E` coming from `D` are the closed cells of `D`. -/
@[simp]
lemma closedCell_relCWComplexTrans_inl (n : ℕ) (i : cell D n) :
    @closedCell X _ C E (relCWComplexTrans C D E h) n
      ((relCWComplexTransCellEquiv h n).symm (.inl i)) = closedCell n i :=
  (rfl)

/-- The closed cells of `C` relative to `E` coming from `C` are the closed cells of `C` relative
to `D`. -/
@[simp]
lemma closedCell_relCWComplexTrans_inr (n : ℕ) (i : cell C n) :
    @closedCell X _ C E (relCWComplexTrans C D E h) n
      ((relCWComplexTransCellEquiv h n).symm (.inr i)) = closedCell n i :=
  (rfl)

/-- The boundaries of the cells of `C` relative to `E` coming from `D` are the boundaries of the
cells of `D`. -/
@[simp]
lemma cellFrontier_relCWComplexTrans_inl (n : ℕ) (i : cell D n) :
    @cellFrontier X _ C E (relCWComplexTrans C D E h) n
      ((relCWComplexTransCellEquiv h n).symm (.inl i)) = cellFrontier n i :=
  (rfl)

/-- The boundaries of the cells of `C` relative to `E` coming from `C` are the boundaries of the
cells of `C` relative to `D`. -/
@[simp]
lemma cellFrontier_relCWComplexTrans_inr (n : ℕ) (i : cell C n) :
    @cellFrontier X _ C E (relCWComplexTrans C D E h) n
      ((relCWComplexTransCellEquiv h n).symm (.inr i)) = cellFrontier n i :=
  (rfl)

end TauCeti
