/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Disjoint.Pairing

/-!
# The disjoint contribution to the pentagon chain-map equation

The two sides of the grid commutation chain-map equation are finite sums over a rectangle
followed by a pentagon and a pentagon followed by a rectangle. When the two domains have
disjoint side pairs, commuting their order gives a bijection. This file uses that bijection
and preservation of the monomial weight to identify the disjoint contributions to the two
sums. The remaining contributions come from domains with a common side.

The juxtaposition argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Section 5.1.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  (R : Type*) [CommSemiring R]

open Classical in
/-- The disjoint rectangle--pentagon and pentagon--rectangle contributions to the
commutation chain-map equation have the same total monomial weight. -/
theorem sum_rectanglePentagonWeight_disjoint_eq_sum_pentagonRectangleWeight_disjoint
    (x z : GridState n) :
    ∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
        (fun D => D.HasDisjointSides), G.rectanglePentagonWeight C R D =
      ∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
        (fun D => D.HasDisjointSides), G.pentagonRectangleWeight C R D := by
  classical
  let e := disjointCommuteEquiv C.column C.turnRow x z
  refine Finset.sum_bij'
    (fun D hD => (e ⟨D, (Finset.mem_filter.mp hD).2⟩).1)
    (fun E hE => (e.symm ⟨E, (Finset.mem_filter.mp hE).2⟩).1) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    have h := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr
      ⟨by simpa only [e, disjointCommuteEquiv_apply] using
          G.commute_mem_pentagonRectangleDecompositions C D h.2 h.1,
        (e ⟨D, h.2⟩).2⟩
  · intro E hE
    have h := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr
      ⟨by simpa only [e, disjointCommuteEquiv_symm_apply] using
          G.commute_mem_rectanglePentagonDecompositions C E h.2 h.1,
        (e.symm ⟨E, h.2⟩).2⟩
  · intro D hD
    exact congrArg Subtype.val (e.left_inv ⟨D, (Finset.mem_filter.mp hD).2⟩)
  · intro E hE
    exact congrArg Subtype.val (e.right_inv ⟨E, (Finset.mem_filter.mp hE).2⟩)
  · intro D hD
    simpa only [e, disjointCommuteEquiv_apply] using
      (G.pentagonRectangleWeight_commute_rectanglePentagon C R D
        (Finset.mem_filter.mp hD).2).symm

end TauCeti.GridDiagram
