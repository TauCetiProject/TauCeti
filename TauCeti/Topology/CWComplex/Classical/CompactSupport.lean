/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# Compact supports in relative CW complexes

A compact subset of a relative CW complex meets only finitely many open cells outside the
base. Consequently it lies in a skeleton of finite dimension, even when the complex is
infinite-dimensional. The base itself need not be compact or finite-dimensional. So the preimages
of the skeleta under a continuous map into the complex absorb every compact set
(`TauCeti.exists_subset_preimageSkeleton_of_isCompact`).

These are the compact-support statements used to pass from skeletal homology to homology
of the whole pair. They do not require local finiteness of the CW structure. The key weak-topology
criterion is that a subset meeting each open cell in a finite set is closed (respectively
discrete) as soon as its intersection with the base is.

## References

* A. Hatcher, *Algebraic Topology*, Appendix, Proposition A.1.
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
  choose x hxK hxO using fun a : A ↦ a.2
  have hx {a : A} {m : ℕ} {j : cell C m} (h : x a ∈ openCell m j) : a.1 = ⟨m, j⟩ :=
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
