/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import TauCeti.Topology.ConnectedComponents

/-!
# Irreducible components of spaces homogeneous on closed points

Let `X` be a Noetherian Jacobson space with a family of homeomorphisms transitive on closed
points. Its irreducible components are pairwise disjoint and clopen, and any two components
are carried to one another by a member of the specified family. In particular they have equal
Krull dimension. No transitivity on nonclosed points, connectedness or finite dimension is assumed.

These results apply to locally closed algebraic orbits over an algebraically closed field,
including orbits of disconnected groups: translations are transitive on their closed points,
although the full scheme space also contains nonclosed points. Disjointness and equal dimension
of the orbit's components are inputs to comparing an orbit with its boundary.

The proofs use Mathlib's open subsets supported on a single irreducible component and
closed-point existence in Jacobson spaces.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.c.
-/

public section

open Set Topology TopologicalSpace

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- An irreducible component meeting an open subset supported on another component equals
that component. -/
theorem eq_of_mem_irreducibleComponents_of_nonempty_inter_open {C D U : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    (hU : IsOpen U) (hUC : U ⊆ C) (hne : (D ∩ U).Nonempty) : D = C := by
  have hDC : D ⊆ C :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hD.1.2 hU hne).trans
      (closure_minimal (inter_subset_right.trans hUC)
        (isClosed_of_mem_irreducibleComponents C hC))
  exact hDC.antisymm (hD.2 hC.1 hDC)

/-- Pairwise disjoint irreducible components of a Noetherian space are clopen. -/
theorem isClopen_of_mem_irreducibleComponents_of_pairwiseDisjoint [NoetherianSpace X]
    (hdisj : (irreducibleComponents X).PairwiseDisjoint id) {C : Set X}
    (hC : C ∈ irreducibleComponents X) : IsClopen C := by
  have : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact isClopen_of_finite_pairwiseDisjoint_closed_cover
    (fun D : irreducibleComponents X ↦ isClosed_of_mem_irreducibleComponents D.1 D.2)
    hdisj.subtype (sUnion_eq_iUnion ▸ sUnion_irreducibleComponents (X := X)) ⟨C, hC⟩

variable [NoetherianSpace X] [JacobsonSpace X] {ι : Type*}

private lemma exists_closedPoint_preimage_eq {C : Set X}
    (hC : C ∈ irreducibleComponents X) :
    ∃ x ∈ closedPoints X ∩ C, ∀ (f : X ≃ₜ X) (Z : Set X),
      Z ∈ irreducibleComponents X → f x ∈ Z → f ⁻¹' Z = C := by
  obtain ⟨U, hU, hUne, hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨x, hxU, hxc⟩ := nonempty_inter_closedPoints hUne hU.isLocallyClosed
  refine ⟨x, ⟨hxc, hUC hxU⟩, fun f Z hZ hxZ ↦ ?_⟩
  exact eq_of_mem_irreducibleComponents_of_nonempty_inter_open hC
    (preimage_mem_irreducibleComponents hZ f.isOpenEmbedding
      (by simpa using hZ.1.nonempty)) hU hUC ⟨x, hxZ, hxU⟩

/-- If a family of homeomorphisms is transitive on closed points, any two irreducible components
are carried to one another by a member of that family. -/
theorem exists_image_eq_of_mem_irreducibleComponents_of_closedPoints_transitive
    (e : ι → X ≃ₜ X)
    (htrans : ∀ x ∈ closedPoints X, ∀ y ∈ closedPoints X, ∃ i, e i x = y) {C D : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X) :
    ∃ i, e i '' C = D := by
  obtain ⟨x, hx, hpre⟩ := exists_closedPoint_preimage_eq hC
  obtain ⟨y, hyD, hyc⟩ := nonempty_inter_closedPoints hD.1.nonempty
    (isClosed_of_mem_irreducibleComponents D hD).isLocallyClosed
  obtain ⟨i, he⟩ := htrans x hx.1 y hyc
  have hEq := hpre (e i) D hD (he.symm ▸ hyD)
  exact ⟨i, by rw [← hEq, (e i).image_preimage]⟩

/-- The irreducible components of a Noetherian Jacobson space homogeneous on closed points
are pairwise disjoint. This includes all points, rather than only closed points. -/
theorem pairwiseDisjoint_irreducibleComponents_of_closedPoints_transitive
    (e : ι → X ≃ₜ X)
    (htrans : ∀ x ∈ closedPoints X, ∀ y ∈ closedPoints X, ∃ i, e i x = y) :
    (irreducibleComponents X).PairwiseDisjoint id := by
  have heq {C D : Set X} (hC : C ∈ irreducibleComponents X)
      (hD : D ∈ irreducibleComponents X) {y : X} (hy : y ∈ closedPoints X)
      (hyC : y ∈ C) (hyD : y ∈ D) : C = D := by
    obtain ⟨x, hx, hpre⟩ := exists_closedPoint_preimage_eq hC
    obtain ⟨i, he⟩ := htrans x hx.1 y hy
    exact (e i).surjective.preimage_injective
      ((hpre (e i) C hC (he.symm ▸ hyC)).trans
        (hpre (e i) D hD (he.symm ▸ hyD)).symm)
  intro C hC D hD hne
  rw [Function.onFun, disjoint_iff_inter_eq_empty]
  by_contra hbad
  obtain ⟨y, hyCD, hyc⟩ := nonempty_inter_closedPoints (nonempty_iff_ne_empty.mpr hbad)
    ((isClosed_of_mem_irreducibleComponents C hC).inter
      (isClosed_of_mem_irreducibleComponents D hD)).isLocallyClosed
  exact hne (heq hC hD hyc hyCD.1 hyCD.2)

/-- Each irreducible component of a Noetherian Jacobson space homogeneous on closed points
is both open and closed. -/
theorem isClopen_of_mem_irreducibleComponents_of_closedPoints_transitive
    (e : ι → X ≃ₜ X)
    (htrans : ∀ x ∈ closedPoints X, ∀ y ∈ closedPoints X, ∃ i, e i x = y) {C : Set X}
    (hC : C ∈ irreducibleComponents X) :
    IsClopen C :=
  isClopen_of_mem_irreducibleComponents_of_pairwiseDisjoint
    (pairwiseDisjoint_irreducibleComponents_of_closedPoints_transitive e htrans) hC

/-- Irreducible components of a Noetherian Jacobson space homogeneous on closed points
have equal topological Krull dimension, even when that dimension is infinite. -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents_of_closedPoints_transitive
    (e : ι → X ≃ₜ X)
    (htrans : ∀ x ∈ closedPoints X, ∀ y ∈ closedPoints X, ∃ i, e i x = y) {C D : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X) :
    topologicalKrullDim C = topologicalKrullDim D := by
  obtain ⟨i, he⟩ :=
    exists_image_eq_of_mem_irreducibleComponents_of_closedPoints_transitive e htrans hC hD
  exact (((e i).image C).trans (Homeomorph.setCongr he)).isHomeomorph.topologicalKrullDim_eq

end TauCeti
