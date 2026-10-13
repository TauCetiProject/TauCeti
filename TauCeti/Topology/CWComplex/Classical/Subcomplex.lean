/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# A CW complex relative to a subcomplex

Let `E` be a subcomplex of a relative CW complex `(C, D)`. Mathlib makes `E` itself a CW complex
relative to `D` (`Topology.RelCWComplex.Subcomplex.instRelCWComplex`), with the cells of `C` that
lie in `E`. This file supplies the complementary structure: `C` is a CW complex relative to `E`,
whose `n`-cells are the `n`-cells of `C` that do not lie in `E`, with the same characteristic maps
(`Topology.RelCWComplex.Subcomplex.relCWComplex`). Together the two structures split the cells of
`C` along `E`; this is how cellular invariants of the pair `(C, E)`, such as relative cellular
homology and the relative Euler characteristic, are computed from those of `C` and `E`.

The structure is not an instance: the base of a relative CW complex is an `outParam`, so `C`
cannot carry one instance for each of its subcomplexes.

A subcomplex `F` contained in another subcomplex `E` uses a subset of the cells of `E`
(`Topology.RelCWComplex.Subcomplex.le_iff_I_subset`), so it is a subcomplex of the CW complex `E`
(`Topology.RelCWComplex.Subcomplex.ofLE`). Combined with the relative structure, this makes `E`
a CW complex relative to `F`, and so lets cellular arguments run along a filtration of `C` by
subcomplexes.

## Main definitions and results

* `Topology.RelCWComplex.Subcomplex.relCWComplex`: the CW structure on `C` relative to a
  subcomplex `E`.
* `Topology.RelCWComplex.Subcomplex.finite_relCWComplex`: it is finite when `C` is.
* `Topology.RelCWComplex.Subcomplex.le_iff_I_subset`: one subcomplex lies in another exactly when
  its cells do.
* `Topology.RelCWComplex.Subcomplex.ofLE`: a subcomplex `F ≤ E`, as a subcomplex of `E`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and Section 2.2, for CW pairs `(X, A)` with `A` a subcomplex.
-/

public section

noncomputable section

open Metric Set

namespace Topology.RelCWComplex.Subcomplex

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- A relative CW complex `(C, D)` is a CW complex relative to any subcomplex `E`: its `n`-cells
are the `n`-cells of `C` that do not lie in `E`, with the characteristic maps of `C`. -/
@[expose, simps, instance_reducible]
def relCWComplex (E : Subcomplex C) : RelCWComplex C E where
  cell n := ↥(E.I n)ᶜ
  map n i := map n (i : cell C n)
  source_eq n i := source_eq n (i : cell C n)
  continuousOn n i := continuousOn n (i : cell C n)
  continuousOn_symm n i := continuousOn_symm n (i : cell C n)
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine pairwiseDisjoint (C := C) (mem_univ ⟨n, i⟩) (mem_univ ⟨m, j⟩) ?_
    exact Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) |>.ne hne
  disjointBase' n i := E.disjoint_openCell_subcomplex_of_notMem i.2
  mapsTo n i := by
    classical
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell (C := C) n (i : cell C n)
    refine ⟨fun m ↦ (J m).subtype (· ∈ (E.I m)ᶜ), ?_⟩
    rw [mapsTo_iff_image_subset]
    intro x hx
    rcases hJ hx with hxD | hx
    · exact Or.inl (E.base_subset hxD)
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨m, hmn, j, hj, hxj⟩ := hx
    by_cases hjE : j ∈ E.I m
    · exact Or.inl (E.closedCell_subset_of_mem hjE hxj)
    · simp only [mem_union, mem_iUnion, exists_prop]
      exact Or.inr ⟨m, hmn, ⟨j, hjE⟩, by simpa using hj, hxj⟩
  closed' A hAC h := by
    refine (RelCWComplex.closed C A hAC).2 ⟨fun n j ↦ ?_, ?_⟩
    · by_cases hj : j ∈ E.I n
      · rw [← inter_eq_right.2 (E.closedCell_subset_of_mem hj), ← inter_assoc]
        exact h.2.inter isClosed_closedCell
      · exact h.1 n ⟨j, hj⟩
    · rw [← inter_eq_right.2 E.base_subset, ← inter_assoc]
      exact h.2.inter (isClosedBase C)
  isClosedBase := E.closed
  union' := by
    refine subset_antisymm (union_subset E.subset_complex
      (iUnion₂_subset fun n j ↦ closedCell_subset_complex n (j : cell C n))) ?_
    refine (RelCWComplex.union (C := C)).superset.trans <|
      union_subset (E.base_subset.trans subset_union_left) (iUnion₂_subset fun n j ↦ ?_)
    by_cases hj : j ∈ E.I n
    · exact (E.closedCell_subset_of_mem hj).trans subset_union_left
    · exact subset_union_of_subset_right
        (subset_iUnion₂ (s := fun n (j : ↥(E.I n)ᶜ) ↦ closedCell n (j : cell C n)) n ⟨j, hj⟩) _

/-- The open cells of `C` relative to `E` are open cells of `C`. -/
@[simp]
lemma openCell_relCWComplex (E : Subcomplex C) (n : ℕ) (i : ↥(E.I n)ᶜ) :
    @openCell X _ C E E.relCWComplex n i = openCell n (i : cell C n) :=
  rfl

/-- The closed cells of `C` relative to `E` are closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (E : Subcomplex C) (n : ℕ) (i : ↥(E.I n)ᶜ) :
    @closedCell X _ C E E.relCWComplex n i = closedCell n (i : cell C n) :=
  rfl

/-- The boundaries of the cells of `C` relative to `E` are boundaries of cells of `C`. -/
@[simp]
lemma cellFrontier_relCWComplex (E : Subcomplex C) (n : ℕ) (i : ↥(E.I n)ᶜ) :
    @cellFrontier X _ C E E.relCWComplex n i = cellFrontier n (i : cell C n) :=
  rfl

/-- The CW structure on `C` relative to a subcomplex is finite dimensional when `C` is. -/
lemma finiteDimensional_relCWComplex [FiniteDimensional C] (E : Subcomplex C) :
    @FiniteDimensional X _ C E E.relCWComplex :=
  @FiniteDimensional.mk X _ C E E.relCWComplex <| by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    simp [isEmpty_subtype]

/-- The CW structure on `C` relative to a subcomplex is of finite type when `C` is. -/
lemma finiteType_relCWComplex [FiniteType C] (E : Subcomplex C) :
    @FiniteType X _ C E E.relCWComplex :=
  @FiniteType.mk X _ C E E.relCWComplex fun n ↦
    have := FiniteType.finite_cell (C := C) (D := D) n
    Subtype.finite

/-- The CW structure on `C` relative to a subcomplex is finite when `C` is. -/
lemma finite_relCWComplex [Finite C] (E : Subcomplex C) :
    @Finite X _ C E E.relCWComplex :=
  @finite_of_finiteDimensional_finiteType X _ C E E.relCWComplex
    (finiteDimensional_relCWComplex E) (finiteType_relCWComplex E)

/-- One subcomplex lies in another exactly when its cells are among the cells of the other. -/
lemma le_iff_I_subset {F E : Subcomplex C} : F ≤ E ↔ ∀ n, F.I n ⊆ E.I n := by
  refine ⟨fun h n i hi ↦ ?_, fun h ↦ ?_⟩
  · by_contra hiE
    obtain ⟨x, hx⟩ := openCell_nonempty (C := C) n i
    exact (E.disjoint_openCell_subcomplex_of_notMem hiE).notMem_of_mem_left hx
      (h (F.openCell_subset_of_mem hi hx))
  · rw [← SetLike.coe_subset_coe, ← F.union, ← E.union]
    exact union_subset_union_right D
      (iUnion_mono fun n ↦ iUnion_mono' fun j ↦ ⟨⟨j, h n j.2⟩, subset_rfl⟩)

/-- A subcomplex `F` of `C` contained in a subcomplex `E`, as a subcomplex of the CW complex `E`.
Its cells are the cells of `E` that are cells of `F`. -/
@[expose, simps]
def ofLE {F E : Subcomplex C} (h : F ≤ E) : Subcomplex (E : Set X) where
  carrier := F
  I n := (Subtype.val : E.I n → cell C n) ⁻¹' F.I n
  closed' := F.closed
  union' := by
    rw [← F.union]
    congr 1
    refine iUnion_congr fun n ↦ iUnion_congr_of_surjective
      (fun j ↦ ⟨(j.1 : E.I n).1, j.2⟩)
      (fun j ↦ ⟨⟨⟨j.1, le_iff_I_subset.1 h n j.2⟩, j.2⟩, rfl⟩) fun j ↦ rfl

end Topology.RelCWComplex.Subcomplex
