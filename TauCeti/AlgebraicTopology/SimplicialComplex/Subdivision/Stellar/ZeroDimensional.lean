/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
public import Mathlib.Data.Set.Card

/-!
# Stellar moves in dimension zero

A stellar move on a complex of dimension at most zero replaces one singleton face by a fresh
singleton face. Consequently stellar equivalence, including injective relabelings in enlarged
vertex types, preserves the number of faces of such a complex. This distinguishes discrete
sets of different cardinalities and supplies the base cases for combinatorial balls and spheres.

The cardinality is `Set.encard`, so no finiteness assumption on the complex or vertex type is
needed; the void complex is included.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (stellar moves and combinatorial balls and spheres).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι}

/-- Starring a face of a zero-dimensional complex replaces just that face by the fresh vertex.
All the faces in this formula are singletons. -/
@[simp]
theorem faces_stellarSubdivision_of_dimension_le_zero (hdim : dimension K ≤ 0)
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    (stellarSubdivision K σ v).faces = insert {v} (K.faces \ {σ}) := by
  obtain ⟨w, rfl⟩ := dimension_le_zero_iff.mp hdim σ hσ
  have hnew : dimension (stellarSubdivision K {w} v) ≤ 0 :=
    (dimension_stellarSubdivision hv (Finset.singleton_nonempty w)).le.trans hdim
  ext τ
  constructor
  · intro hτ
    obtain ⟨x, rfl⟩ := dimension_le_zero_iff.mp hnew τ hτ
    by_cases hx : x = v
    · subst x
      exact Set.mem_insert _ _
    · have hvx : v ∉ ({x} : Finset ι) := by simpa [eq_comm] using hx
      obtain ⟨hK, havoid⟩ := mem_stellarSubdivision_iff_of_notMem hvx |>.mp hτ
      exact Set.mem_insert_of_mem _ ⟨hK, fun he => havoid (he ▸ Finset.Subset.rfl)⟩
  · rintro (rfl | ⟨hτ, hne⟩)
    · exact singleton_mem_stellarSubdivision_iff.mpr hσ
    · obtain ⟨x, rfl⟩ := dimension_le_zero_iff.mp hdim τ hτ
      have hvx := notMem_of_singleton_notMem hv hτ
      apply mem_stellarSubdivision_iff_of_notMem hvx |>.mpr
      refine ⟨hτ, ?_⟩
      intro hsub
      have hwx : w = x := Finset.singleton_subset_singleton.mp hsub
      exact hne (by simp [hwx])

/-- Stellar equivalence preserves the face cardinality in dimension at most zero. -/
theorem StellarEquivalent.encard_faces_eq_of_dimension_le_zero
    (h : StellarEquivalent K L) (hdim : dimension K ≤ 0) :
    L.faces.encard = K.faces.encard := by
  suffices hc : dimension L = dimension K ∧
      (dimension K ≤ 0 → L.faces.encard = K.faces.encard) from hc.2 hdim
  apply h.induction_on
  · intro A B h
    refine ⟨h.dimension_eq, ?_⟩
    intro hd
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp h
    rw [faces_stellarSubdivision_of_dimension_le_zero hd hσ hv]
    exact Set.encard_exchange hv hσ
  · intro A
    exact ⟨rfl, fun _ => rfl⟩
  · intro A B ih
    exact ⟨ih.1.symm, fun hd => (ih.2 (ih.1.symm.le.trans hd)).symm⟩
  · intro A B C ihAB ihBC
    exact ⟨ihBC.1.trans ihAB.1,
      fun hd => (ihBC.2 (ihAB.1.le.trans hd)).trans (ihAB.2 hd)⟩

/-- Intrinsic stellar equivalence preserves the face cardinality in dimension at most zero,
even when its generators relabel the complexes in a larger vertex type. -/
theorem StellarEquivalentUpToRelabeling.encard_faces_eq_of_dimension_le_zero
    (h : StellarEquivalentUpToRelabeling K L) (hdim : dimension K ≤ 0) :
    L.faces.encard = K.faces.encard := by
  suffices hc : dimension L = dimension K ∧
      (dimension K ≤ 0 → L.faces.encard = K.faces.encard) from hc.2 hdim
  apply h.induction_on
  · intro A B f g he
    have hdB := dimension_map_of_injective (K := B) g g.injective
    have hdA := dimension_map_of_injective (K := A) f f.injective
    refine ⟨hdB.symm.trans (he.dimension_eq.trans hdA), ?_⟩
    intro hd
    have hc := he.encard_faces_eq_of_dimension_le_zero (hdA.le.trans hd)
    simpa only [faces_map, (Finset.image_injective f.injective).encard_image,
      (Finset.image_injective g.injective).encard_image] using hc
  · intro A
    exact ⟨rfl, fun _ => rfl⟩
  · intro A B ih
    exact ⟨ih.1.symm, fun hd => (ih.2 (ih.1.symm.le.trans hd)).symm⟩
  · intro A B C ihAB ihBC
    exact ⟨ihBC.1.trans ihAB.1,
      fun hd => (ihBC.2 (ihAB.1.le.trans hd)).trans (ihAB.2 hd)⟩

end PreAbstractSimplicialComplex
