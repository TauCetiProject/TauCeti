/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Compact supports in relative CW complexes

A compact subset of a relative CW complex meets only finitely many open cells outside the
base. Consequently it lies in a skeleton of finite dimension, even when the complex is
infinite-dimensional. The base itself need not be compact or finite-dimensional.

These are the compact-support statements used to pass from skeletal homology to homology
of the whole pair. They do not require local finiteness of the CW structure. The key weak-topology
criterion is that a subset disjoint from the base and meeting each open cell in a finite set
is closed and discrete.

## References

* A. Hatcher, *Algebraic Topology*, Appendix, Proposition A.1.
-/

public section

open Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D S : Set X}
  [RelCWComplex C D]

/-- A subset of a relative CW complex disjoint from its base is closed if it meets each open
cell in a finite set. -/
lemma isClosed_of_finite_inter_openCell (hSC : S ⊆ C) (hSD : Disjoint S D)
    (hS : ∀ n (i : cell C n), (S ∩ openCell n i).Finite) : IsClosed S := by
  refine isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hSC ?_
    (fun n _ i ↦ Or.inl (hS n i).isClosed)
  simpa only [Set.disjoint_iff_inter_eq_empty.1 hSD] using isClosed_empty

/-- A subset of a relative CW complex disjoint from its base is discrete if it meets each open
cell in a finite set. -/
lemma isDiscrete_of_finite_inter_openCell (hSC : S ⊆ C) (hSD : Disjoint S D)
    (hS : ∀ n (i : cell C n), (S ∩ openCell n i).Finite) : IsDiscrete S := by
  refine isDiscrete_iff_forall_mem_exists_isClosed.2 fun T hTS ↦ ?_
  exact ⟨T, isClosed_of_finite_inter_openCell (hTS.trans hSC) (hSD.mono_left hTS)
    (fun n i ↦ (hS n i).subset (inter_subset_inter_left _ hTS)),
    inter_eq_left.2 hTS⟩

/-- A compact subset of the ambient space meets only finitely many relative open cells.
There is no local-finiteness or dimension assumption, and the base is excluded from the cell
indexing. -/
theorem finite_setOf_nonempty_inter_openCell_of_isCompact {K : Set X} (hK : IsCompact K) :
    {a : Σ n, cell C n | (K ∩ openCell a.1 a.2).Nonempty}.Finite := by
  classical
  let A := {a : Σ n, cell C n | (K ∩ openCell a.1 a.2).Nonempty}
  choose x hx using fun a : A ↦ a.2
  have hxK (a : A) : x a ∈ K := (hx a).1
  have hxO (a : A) : x a ∈ openCell a.1.1 a.1.2 := (hx a).2
  have hxinj : Function.Injective x := by
    intro a b hab
    by_contra h
    exact (disjoint_openCell_of_ne (Subtype.val_injective.ne h)).ne_of_mem
      (hxO a) (hxO b) hab
  have hSD : Disjoint (range x) D := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ hxD
    exact Set.disjoint_left.1 (disjointBase a.1.1 a.1.2) (hxO a) hxD
  have hS (n : ℕ) (i : cell C n) : (range x ∩ openCell n i).Finite := by
    by_cases h : (K ∩ openCell n i).Nonempty
    · let a : A := ⟨⟨n, i⟩, h⟩
      refine (finite_singleton (x a)).subset ?_
      rintro y ⟨⟨b, rfl⟩, hbi⟩
      have hba : b = a := by
        apply Subtype.ext
        by_contra hne
        exact Set.disjoint_left.1 (disjoint_openCell_of_ne hne) (hxO b) hbi
      simp only [hba, mem_singleton_iff]
    · refine finite_empty.subset ?_
      rintro y ⟨⟨a, rfl⟩, hai⟩
      exact (h ⟨x a, hxK a, hai⟩).elim
  have hSC : range x ⊆ C := by
    rintro _ ⟨a, rfl⟩
    exact openCell_subset_complex _ _ (hxO a)
  have hclosed := isClosed_of_finite_inter_openCell hSC hSD hS
  have hdiscrete := isDiscrete_of_finite_inter_openCell hSC hSD hS
  have hcompact : IsCompact (range x) :=
    hK.of_isClosed_subset hclosed (by rintro _ ⟨a, rfl⟩; exact hxK a)
  have : Finite A := (Set.finite_range_iff hxinj).1 (hcompact.finite hdiscrete)
  exact Set.toFinite A

/-- Every compact subset of a relative CW complex is contained in a skeleton of finite
relative dimension. The skeleton contains the entire base, so no restriction on the base is
needed. -/
theorem exists_subset_skeletonLT_of_isCompact {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ n : ℕ, K ⊆ (skeletonLT C (n : ℕ∞) : Set X) := by
  classical
  let A := {a : Σ n, cell C n | (K ∩ openCell a.1 a.2).Nonempty}
  have hA : A.Finite := finite_setOf_nonempty_inter_openCell_of_isCompact (C := C) hK
  refine ⟨hA.toFinset.sup Sigma.fst + 1, fun x hx ↦ ?_⟩
  have hxC := hKC hx
  rw [← union_iUnion_openCell_eq_complex (C := C)] at hxC
  rcases hxC with hxD | hxC
  · exact (skeletonLT C _).base_subset hxD
  · obtain ⟨m, i, hxi⟩ := by simpa only [mem_iUnion] using hxC
    refine mem_skeletonLT_iff.2 (Or.inr ⟨m, ?_, i, hxi⟩)
    have hmem : (⟨m, i⟩ : Σ n, cell C n) ∈ hA.toFinset := hA.mem_toFinset.2 ⟨x, hx, hxi⟩
    exact_mod_cast Nat.lt_succ_of_le (Finset.le_sup (f := Sigma.fst) hmem)

end TauCeti
