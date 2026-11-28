/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
public import TauCeti.Topology.CWComplex.Classical.Subcomplex

/-!
# Compact supports in relative CW complexes

A compact subset of a relative CW complex meets only finitely many open cells outside the
base; in particular, in a Hausdorff ambient space the closure of every open cell meets only
finitely many open cells (`TauCeti.finite_setOf_nonempty_closure_openCell_inter_openCell`).
Consequently every compact subset lies in a skeleton of finite dimension, even when the complex is
infinite-dimensional. The base itself need not be compact or finite-dimensional. So the preimages
of the skeleta under a continuous map into the complex absorb every compact set
(`TauCeti.exists_subset_preimageSkeleton_of_isCompact`).

For an absolute Hausdorff CW complex `C`, every cell `(n, i)` is contained in a recursive finite
subcomplex `Topology.CWComplex.cellSubcomplex n i` built from the lower-dimensional cells whose open
cells meet `cellFrontier n i` (`Topology.CWComplex.mem_cellSubcomplex_iff`). Combining this with
`TauCeti.finite_setOf_nonempty_inter_openCell_of_isCompact`, every compact subset of `C` is
contained in a finite subcomplex (`Topology.CWComplex.exists_finite_subcomplex_of_isCompact`).

These are the compact-support statements used to pass from skeletal homology to homology
of the whole pair and to build finite-subcomplex covers. They do not require local finiteness of the
CW structure. The key weak-topology criterion is that a subset meeting each open cell in a finite
set is closed (respectively discrete) as soon as its intersection with the base is.

## References

* R. Fritsch, R. A. Piccinini, *Cellular Structures in Topology*, Cambridge University Press (1990),
  Theorem 1.5.14.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Proposition A.1.
-/

public section

open Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D S : Set X}
  [RelCWComplex C D]

/-- A subset of a relative CW complex is closed if it meets each open cell in a finite set and
meets the base in a closed set. -/
lemma isClosed_of_finite_inter_openCell (hSC : S ⊆ C) (hSD : IsClosed (S ∩ D))
    (hS : ∀ n (i : cell C n), (S ∩ openCell n i).Finite) : IsClosed S :=
  isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hSC hSD
    fun n _ i ↦ Or.inl (hS n i).isClosed

/-- A subset of a relative CW complex is discrete if it meets each open cell in a finite set and
meets the base in a discrete set. -/
lemma isDiscrete_of_finite_inter_openCell (hSC : S ⊆ C) (hSD : IsDiscrete (S ∩ D))
    (hS : ∀ n (i : cell C n), (S ∩ openCell n i).Finite) : IsDiscrete S := by
  refine isDiscrete_iff_forall_mem_exists_isClosed.2 fun T hTS ↦ ?_
  obtain ⟨U, hU, hUT⟩ :=
    isDiscrete_iff_forall_mem_exists_isClosed.1 hSD (T ∩ D) (inter_subset_inter_left _ hTS)
  -- The part of `T` off the base is closed by the previous lemma; on the base, `U` cuts out `T`.
  have hTD : IsClosed (T \ D) :=
    isClosed_of_finite_inter_openCell (sdiff_subset.trans (hTS.trans hSC))
      (by simpa only [sdiff_inter_self] using isClosed_empty)
      fun n i ↦ (hS n i).subset (inter_subset_inter_left _ (sdiff_subset.trans hTS))
  refine ⟨U ∩ D ∪ T \ D, (hU.inter (isClosedBase C)).union hTD, ?_⟩
  ext x
  have hx := Set.ext_iff.1 hUT x
  have := @hTS x
  simp only [mem_union, mem_inter_iff, mem_sdiff] at hx ⊢
  tauto

/-- A compact subset of the ambient space meets only finitely many relative open cells.
There is no local-finiteness or dimension assumption, and the base is excluded from the cell
indexing. -/
theorem finite_setOf_nonempty_inter_openCell_of_isCompact {K : Set X} (hK : IsCompact K) :
    {a : Σ n, cell C n | (K ∩ openCell a.1 a.2).Nonempty}.Finite := by
  let A := {a : Σ n, cell C n | (K ∩ openCell a.1 a.2).Nonempty}
  -- Pick a point `x a` of `K` in each open cell `a` that `K` meets.
  choose x hxK hxO using fun a : A ↦ a.property
  have hx {a : A} {m : ℕ} {j : cell C m} (h : x a ∈ openCell m j) : a.val = ⟨m, j⟩ :=
    eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨x a, hxO a, h⟩)
  have hxinj : Function.Injective x := fun a b hab ↦ Subtype.ext (hx (hab ▸ hxO b))
  have hSC : range x ⊆ C := range_subset_iff.2 fun a ↦ openCell_subset_complex _ _ (hxO a)
  have hSD : (range x ∩ D).Finite := finite_empty.subset <| by
    rintro _ ⟨⟨a, rfl⟩, hD⟩
    exact disjoint_left.1 (disjointBase _ _) (hxO a) hD
  have hS (n : ℕ) (i : cell C n) : (range x ∩ openCell n i).Finite := by
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨⟨a, rfl⟩, ha⟩ _ ⟨⟨b, rfl⟩, hb⟩
    exact congrArg x (Subtype.ext ((hx ha).trans (hx hb).symm))
  -- So the chosen points form a closed discrete subset of the compact set `K`.
  have hcompact : IsCompact (range x) :=
    hK.of_isClosed_subset (isClosed_of_finite_inter_openCell hSC hSD.isClosed hS)
      (range_subset_iff.2 hxK)
  have : Finite A := (finite_range_iff hxinj).1
    (hcompact.finite (isDiscrete_of_finite_inter_openCell hSC hSD.isDiscrete hS))
  exact Set.toFinite A

/-- In a Hausdorff relative CW complex, the closure of every open cell meets only finitely many
relative open cells. -/
theorem finite_setOf_nonempty_closure_openCell_inter_openCell (n : ℕ) (i : cell C n) :
    {a : Σ m, cell C m | (closure (openCell n i) ∩ openCell a.1 a.2).Nonempty}.Finite := by
  rw [closure_openCell_eq_closedCell]
  exact finite_setOf_nonempty_inter_openCell_of_isCompact isCompact_closedCell

/-- Every compact subset of a relative CW complex is contained in a skeleton of finite
relative dimension. The skeleton contains the entire base, so no restriction on the base is
needed. -/
theorem exists_subset_skeletonLT_of_isCompact {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ n : ℕ, K ⊆ (skeletonLT C (n : ℕ∞) : Set X) := by
  obtain ⟨N, hN⟩ :=
    ((finite_setOf_nonempty_inter_openCell_of_isCompact (C := C) hK).image Sigma.fst).bddAbove
  refine ⟨N + 1, fun x hx ↦ ?_⟩
  have hxC := hKC hx
  rw [← union_iUnion_openCell_eq_complex (C := C)] at hxC
  rcases hxC with hxD | hxC
  · exact (skeletonLT C _).base_subset hxD
  · obtain ⟨m, i, hxi⟩ := by simpa only [mem_iUnion] using hxC
    refine mem_skeletonLT_iff.2 (Or.inr ⟨m, ?_, i, hxi⟩)
    exact_mod_cast Nat.lt_succ_of_le (hN ⟨⟨m, i⟩, ⟨x, hx, hxi⟩, rfl⟩)

/-- **The skeletal filtration absorbs compact sets.** If `f` is continuous with values in the
complex `C`, every compact subset of `E` lies in the preimage of some skeleton, since its image is
compact and so lies in a finite skeleton. -/
lemma exists_subset_preimageSkeleton_of_isCompact {E : Type*} [TopologicalSpace E] {f : E → X}
    (hf : Continuous f) (hfC : Set.range f ⊆ C) {K : Set E} (hK : IsCompact K) :
    ∃ q, K ⊆ preimageSkeleton C f q := by
  obtain ⟨n, hn⟩ := exists_subset_skeletonLT_of_isCompact (hK.image hf)
    ((Set.image_subset_range f K).trans hfC)
  refine ⟨n, fun x hx ↦ ?_⟩
  rw [preimageSkeleton_natCast]
  exact skeletonLT_mono le_self_add (hn (mem_image_of_mem f hx))

end TauCeti

namespace Topology.CWComplex

noncomputable section FiniteSubcomplex

variable {X : Type*} [TopologicalSpace X] {C : Set X} [CWComplex C]

/-- Finite set of `m`-cells (`m < n`) whose open cells meet `cellFrontier n i` and together cover
`cellFrontier n i`. -/
private def frontierCells (n : ℕ) (i : cell C n) (m : ℕ) : Finset (cell C m) :=
  open Classical in
  ((cellFrontier_subset_finite_openCell (C := C) n i).choose m).filter
    fun j ↦ (cellFrontier n i ∩ openCell m j).Nonempty

private lemma mem_frontierCells_iff {n m : ℕ} {i : cell C n} {j : cell C m} :
    j ∈ frontierCells n i m ↔ (cellFrontier n i ∩ openCell m j).Nonempty := by
  classical
  refine ⟨fun hj ↦ (Finset.mem_filter.1 hj).2, fun ⟨x, hxf, hxo⟩ ↦ ?_⟩
  obtain ⟨m', -, j', hj', hx'⟩ := by
    simpa only [mem_iUnion, exists_prop] using
      (cellFrontier_subset_finite_openCell (C := C) n i).choose_spec hxf
  have hmj : (⟨m, j⟩ : Σ k, cell C k) = ⟨m', j'⟩ :=
    RelCWComplex.eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨x, hxo, hx'⟩)
  obtain rfl : m = m' := congrArg Sigma.fst hmj
  obtain rfl : j = j' := eq_of_heq (Sigma.ext_iff.1 hmj).2
  exact Finset.mem_filter.2 ⟨hj', ⟨x, hxf, hxo⟩⟩

private lemma cellFrontier_subset_iUnion_frontierCells (n : ℕ) (i : cell C n) :
    cellFrontier n i ⊆ ⋃ (m : Fin n) (j ∈ frontierCells n i m.val), openCell m.val j :=
  fun x hx ↦ by
    classical
    obtain ⟨m, hmn, j, hj, hxj⟩ := by
      simpa only [mem_iUnion, exists_prop] using
        (cellFrontier_subset_finite_openCell (C := C) n i).choose_spec hx
    exact mem_iUnion.2 ⟨⟨m, hmn⟩, mem_iUnion₂.2 ⟨j, Finset.mem_filter.2 ⟨hj, ⟨x, hx, hxj⟩⟩, hxj⟩⟩

variable [T2Space X]

/-- Bundled finite subcomplex containing `closedCell n i`, constructed recursively along cell
dimension so that every cell used at step `n` meets `closedCell n i`. -/
private def cellSubcomplexAux :
    ∀ (n : ℕ) (i : cell C n), {E : Subcomplex C // Finite (E : Set X) ∧ closedCell n i ⊆ E}
  | n, i =>
    open Classical in
    let B : Subcomplex C :=
      (Finset.univ : Finset (Fin n)).sup fun m ↦
        (frontierCells n i m.val).sup fun j ↦ (cellSubcomplexAux m.val j).val
    have hB_fin : Finite (B : Set X) :=
      Subcomplex.finite_finsetSup _ _ fun m _ ↦
        Subcomplex.finite_finsetSup _ _ fun j _ ↦ (cellSubcomplexAux m.val j).property.1
    have hB_fr : cellFrontier n i ⊆ B :=
      (cellFrontier_subset_iUnion_frontierCells n i).trans <| iUnion_subset fun m ↦
        iUnion₂_subset fun j hj ↦ (RelCWComplex.openCell_subset_closedCell m.val j).trans <|
          (cellSubcomplexAux m.val j).property.2.trans <|
            (Finset.le_sup (f := fun k ↦ (cellSubcomplexAux m.val k).val) hj).trans <|
              Finset.le_sup (f := fun m : Fin n ↦
                (frontierCells n i m.val).sup fun k ↦ (cellSubcomplexAux m.val k).val)
                (Finset.mem_univ m)
    ⟨B.adjoinCell n i hB_fr, RelCWComplex.Subcomplex.finite_adjoinCell hB_fin n i hB_fr,
      by rw [RelCWComplex.Subcomplex.coe_adjoinCell]; exact subset_union_right⟩
termination_by n _ => n
decreasing_by all_goals exact Fin.is_lt _

/-- A finite subcomplex of `C` containing `closedCell n i`, built recursively from the lower
dimensional cells meeting `cellFrontier n i`. -/
def cellSubcomplex (n : ℕ) (i : cell C n) : Subcomplex C := (cellSubcomplexAux n i).val

/-- For each cell `(n, i)`, the subcomplex `cellSubcomplex n i` is finite. -/
instance finite_cellSubcomplex (n : ℕ) (i : cell C n) : Finite (cellSubcomplex n i : Set X) :=
  (cellSubcomplexAux n i).property.1

/-- The closed cell `closedCell n i` is contained in `cellSubcomplex n i`. -/
theorem closedCell_subset_cellSubcomplex (n : ℕ) (i : cell C n) :
    closedCell n i ⊆ cellSubcomplex n i := (cellSubcomplexAux n i).property.2

private lemma coe_cellSubcomplex_eq (n : ℕ) (i : cell C n) :
    (cellSubcomplex n i : Set X) =
      (⋃ (m : Fin n) (j ∈ frontierCells n i m.val), (cellSubcomplex m.val j : Set X)) ∪
        closedCell n i := by
  unfold cellSubcomplex
  rw [cellSubcomplexAux]
  simp [RelCWComplex.Subcomplex.coe_finsetSup]

/-- A point lies in `cellSubcomplex n i` if and only if it lies in `closedCell n i` or in
`cellSubcomplex m j` for some lower-dimensional cell `(m, j)` (`m < n`) whose open cell meets
`cellFrontier n i`. -/
theorem mem_cellSubcomplex_iff {n : ℕ} {i : cell C n} {x : X} :
    x ∈ cellSubcomplex n i ↔
      x ∈ closedCell n i ∨
        ∃ (m : ℕ) (_ : m < n) (j : cell C m),
          (cellFrontier n i ∩ openCell m j).Nonempty ∧ x ∈ cellSubcomplex m j := by
  rw [← SetLike.mem_coe, coe_cellSubcomplex_eq, mem_union, or_comm]
  refine or_congr_right ?_
  simp only [mem_iUnion, exists_prop, Fin.exists_iff, mem_frontierCells_iff, SetLike.mem_coe]

/-- **Every compact subset of a Hausdorff CW complex is contained in a finite subcomplex.** No
local-finiteness or dimension bound is required on `C`. -/
theorem exists_finite_subcomplex_of_isCompact {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ E : Subcomplex C, Finite (E : Set X) ∧ K ⊆ E := by
  classical
  have hfin := TauCeti.finite_setOf_nonempty_inter_openCell_of_isCompact (C := C) hK
  refine ⟨hfin.toFinset.sup fun p ↦ cellSubcomplex p.1 p.2,
    Subcomplex.finite_finsetSup _ _ fun p _ ↦ finite_cellSubcomplex p.1 p.2, fun x hx ↦ ?_⟩
  obtain ⟨n, i, hxi⟩ := mem_iUnion₂.1 (iUnion_openCell_eq_complex (C := C) ▸ hKC hx)
  exact Finset.le_sup (f := fun p : Σ m, cell C m ↦ cellSubcomplex p.1 p.2)
    (b := ⟨n, i⟩) (hfin.mem_toFinset.2 ⟨x, hx, hxi⟩)
    (closedCell_subset_cellSubcomplex n i (RelCWComplex.openCell_subset_closedCell n i hxi))

end FiniteSubcomplex

end Topology.CWComplex
