/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Disjoint
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing
import Mathlib.Algebra.CharP.Two

/-!
# Recut pairing of hexagon--rectangle terms in the commutation homotopy equation

The left-hand side `∂ ∘ H + H ∘ ∂` of the homotopy equation of a column commutation counts two-step
domains made of a commutation hexagon and a rectangle of the original diagram, in either order.
Forgetting the two turns of the hexagon leaves a two-step rectangle decomposition. When its two
rectangles share exactly one side column, their union is an L-shaped domain, and the recut from
the proof of `∂² = 0` cuts it the other way (`TauCeti.GridRectangleDecomposition.recut`).

Both orders of composition lie on the same side of the equation, so they are treated as one
family, `TauCeti.GridHexagonCompositeDecomposition`. If the recut of a counted composite is again
the underlying decomposition of a counted composite, the two terms cancel in characteristic two,
whatever the orientation of their common side and whichever piece of the recut carries the
hexagon. The weights agree because both terms cover the same squares and their rectangles carry
the same single `X`-marking, that of the column the hexagon cuts away
(`TauCeti.GridCommutationHexagonBetween.cutColumn`): this fixes the variable by which the
underlying rectangle weight exceeds the composite weight. A counted composite determines the
position of its hexagon from its underlying decomposition, since a counted rectangle carries no
`X`-marking while the rectangle under a counted hexagon carries one. Hence recut partners form a
fixed-point-free involution.

Off the diagonal, what remains of the hexagon side are the composites whose recut is not again a
counted composite (`TauCeti.GridDiagram.unpairedHexagonComposites`). In the juxtaposition argument
these are the terms matched with the pairs of pentagons counted by the round trip `Ψ ∘ Φ` of the
two commutation maps; that matching is not part of this file.

## Main definition

* `TauCeti.GridDiagram.unpairedHexagonComposites`: the counted composites sharing a side column
  whose recut underlies no counted composite.

## Main results

* `TauCeti.GridDiagram.sum_hexagonCompositeWeight_overlap_eq_sum_unpaired`: in characteristic two,
  the off-diagonal overlapping composites have the total weight of the unpaired ones.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_unpaired`: the homotopy
  equation is equivalent to its diagonal identity together with the identity between the unpaired
  composites and the pentagon pairs off the diagonal.

## References

This is the juxtaposition argument for the homotopy of Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Section 5.1, and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link
Floer homology*, Section 3.1 (arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

variable (R : Type*) [CommSemiring R]

open scoped Classical in
/-- The overlapping counted composites have the total weight of the overlapping
hexagon--rectangle and rectangle--hexagon decompositions. -/
theorem sum_hexagonCompositeWeight_filter_not_hasDisjointSides (x z : GridState n) :
    ∑ D ∈ (G.hexagonCompositeDecompositions C x z).filter
        (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.hexagonCompositeWeight C R D =
      (∑ D ∈ (G.hexagonRectangleDecompositions C x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.hexagonRectangleWeight C R D) +
        ∑ D ∈ (G.rectangleHexagonDecompositions C x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.rectangleHexagonWeight C R D := by
  have hdecomp : G.hexagonCompositeDecompositions C x z =
      (G.hexagonRectangleDecompositions C x z).disjSum
        (G.rectangleHexagonDecompositions C x z) := by
    ext D
    cases D <;> simp
  simp only [Finset.sum_filter, hdecomp, Finset.sum_disjSum,
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
    hexagonCompositeWeight_inl, hexagonCompositeWeight_inr]

/-! ### The recut pairing -/

/-- The counted composites from `x` to `z` whose two rectangles have a common side column and
whose recut is not the underlying rectangle decomposition of any counted composite. -/
noncomputable def unpairedHexagonComposites (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z) := by
  classical
  exact (G.hexagonCompositeDecompositions C x z).filter fun D =>
    ¬D.toRectangleDecomposition.HasDisjointSides ∧
      ∀ E ∈ G.hexagonCompositeDecompositions C x z,
        ¬D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition

/-- A composite is unpaired exactly when it is counted, its rectangles have a common side column,
and its recut underlies no counted composite. -/
@[simp]
theorem mem_unpairedHexagonComposites {x z : GridState n}
    (D : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    D ∈ G.unpairedHexagonComposites C x z ↔
      D ∈ G.hexagonCompositeDecompositions C x z ∧
        ¬D.toRectangleDecomposition.HasDisjointSides ∧
          ∀ E ∈ G.hexagonCompositeDecompositions C x z,
            ¬D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [unpairedHexagonComposites, Finset.mem_filter]

/-- Off the diagonal, a recut partner of a counted overlapping composite is again overlapping,
has the original composite as its own recut partner, has the same weight, and is different from
it. -/
private theorem recut_partner {x z : GridState n} (hzx : z ≠ x)
    {D E : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z)
    (hdisj : ¬D.toRectangleDecomposition.HasDisjointSides)
    (hE : E ∈ G.hexagonCompositeDecompositions C x z)
    (h : D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition) :
    E.toRectangleDecomposition.IsRecut D.toRectangleDecomposition ∧
      ¬E.toRectangleDecomposition.HasDisjointSides ∧
        G.hexagonCompositeWeight C R E = G.hexagonCompositeWeight C R D ∧ E ≠ D := by
  have hone := (D.toRectangleDecomposition.hasDisjointSides_or_hasOneCommonSide_of_ne
    hzx).resolve_left hdisj
  obtain ⟨hfirst, hsecond⟩ := G.isEmpty_of_mem_hexagonCompositeDecompositions C hD
  have hsymm := h.symm hone hfirst hsecond
  refine ⟨hsymm, ?_, ?_, fun hED => h.middle_ne (by rw [hED])⟩
  · exact E.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide
      (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hsymm hzx)
  · exact G.hexagonCompositeWeight_eq_of_isRepartition C R hE hD hsymm.isRepartition

/-- Off the diagonal, a counted overlapping composite has at most one recut partner among the
counted composites. -/
private theorem eq_of_isRecut_of_isRecut {x z : GridState n} (hzx : z ≠ x)
    {D E E' : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z)
    (hdisj : ¬D.toRectangleDecomposition.HasDisjointSides)
    (hE : E ∈ G.hexagonCompositeDecompositions C x z)
    (hE' : E' ∈ G.hexagonCompositeDecompositions C x z)
    (h : D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition)
    (h' : D.toRectangleDecomposition.IsRecut E'.toRectangleDecomposition) : E = E' := by
  have hone := (D.toRectangleDecomposition.hasDisjointSides_or_hasOneCommonSide_of_ne
    hzx).resolve_left hdisj
  obtain ⟨hfirst, hsecond⟩ := G.isEmpty_of_mem_hexagonCompositeDecompositions C hD
  exact G.injOn_toRectangleDecomposition_hexagonCompositeDecompositions C x z hE hE'
    ((D.toRectangleDecomposition.existsUnique_isRecut hone hfirst hsecond).unique h h')

variable [CharP R 2]

open scoped Classical in
/-- Off the diagonal and in characteristic two, the counted composites whose rectangles share a
side column have the total weight of the unpaired ones: recut partners cancel in pairs. -/
theorem sum_hexagonCompositeWeight_overlap_eq_sum_unpaired {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ (G.hexagonCompositeDecompositions C x z).filter
        (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.hexagonCompositeWeight C R D =
      ∑ D ∈ G.unpairedHexagonComposites C x z, G.hexagonCompositeWeight C R D := by
  set S := (G.hexagonCompositeDecompositions C x z).filter
    (fun D => ¬D.toRectangleDecomposition.HasDisjointSides)
  have hunpaired : S.filter (fun D => ¬∃ E ∈ G.hexagonCompositeDecompositions C x z,
      D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition) =
        G.unpairedHexagonComposites C x z := by
    ext D
    simp only [S, Finset.mem_filter, mem_unpairedHexagonComposites, not_exists, not_and,
      and_assoc]
  -- The paired composites cancel under the involution sending each to its recut partner.
  have hpartner : ∀ D ∈ S.filter (fun D => ∃ E ∈ G.hexagonCompositeDecompositions C x z,
      D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition),
      ∃ E ∈ G.hexagonCompositeDecompositions C x z,
        D ∈ G.hexagonCompositeDecompositions C x z ∧
          ¬D.toRectangleDecomposition.HasDisjointSides ∧
            D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := fun D hD => by
    obtain ⟨hDS, E, hE, hrecut⟩ := Finset.mem_filter.mp hD
    exact ⟨E, hE, (Finset.mem_filter.mp hDS).1, (Finset.mem_filter.mp hDS).2, hrecut⟩
  have hpaired : ∑ D ∈ S.filter (fun D => ∃ E ∈ G.hexagonCompositeDecompositions C x z,
      D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition),
      G.hexagonCompositeWeight C R D = 0 := by
    have hmem : ∀ D hD, (hpartner D hD).choose ∈ S.filter
        (fun D => ∃ E ∈ G.hexagonCompositeDecompositions C x z,
          D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition) := fun D hD => by
      obtain ⟨hE, hD, hdisj, hrecut⟩ := (hpartner D hD).choose_spec
      obtain ⟨hsymm, hEdisj, -, -⟩ := G.recut_partner C R hzx hD hdisj hE hrecut
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hE, hEdisj⟩, _, hD, hsymm⟩
    refine Finset.sum_involution (fun D hD => (hpartner D hD).choose) ?_ ?_ hmem ?_
    · intro D hD
      obtain ⟨hE, hD, hdisj, hrecut⟩ := (hpartner D hD).choose_spec
      rw [(G.recut_partner C R hzx hD hdisj hE hrecut).2.2.1]
      exact CharTwo.add_self_eq_zero _
    · intro D hD _
      obtain ⟨hE, hD, hdisj, hrecut⟩ := (hpartner D hD).choose_spec
      exact (G.recut_partner C R hzx hD hdisj hE hrecut).2.2.2
    · intro D hD
      obtain ⟨hE, hD', hdisj, hrecut⟩ := (hpartner D hD).choose_spec
      obtain ⟨hsymm, hEdisj, -, -⟩ := G.recut_partner C R hzx hD' hdisj hE hrecut
      obtain ⟨hF, -, -, hFrecut⟩ := (hpartner _ (hmem D hD)).choose_spec
      exact G.eq_of_isRecut_of_isRecut C hzx hE hEdisj hF hD' hFrecut hsymm
  rw [← Finset.sum_filter_add_sum_filter_not S (fun D => ∃ E ∈ G.hexagonCompositeDecompositions
    C x z, D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition), hpaired, zero_add,
    hunpaired]

open scoped Classical in
/-- In characteristic two, the commutation homotopy equation is equivalent to its diagonal
coefficient identity together with the off-diagonal identity between the unpaired hexagon
composites and the pentagon pairs. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff_unpaired :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns C.column (finRotate n C.column)).commutationMap R C.reverse
          (G.commutationMap R C c)) ↔
      (∀ x : GridState n,
        (∑ D ∈ G.hexagonRectangleDecompositions C x x, G.hexagonRectangleWeight C R D) +
            ∑ D ∈ G.rectangleHexagonDecompositions C x x,
              G.rectangleHexagonWeight C R D =
          1 + ∑ D ∈ G.pentagonPairDecompositions C x x, G.pentagonPairWeight C R D) ∧
      ∀ x z : GridState n, z ≠ x →
        ∑ D ∈ G.unpairedHexagonComposites C x z, G.hexagonCompositeWeight C R D =
          ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  rw [G.unblockedDifferential_commutationHomotopy_add_eq_iff_overlap C R]
  have hoff : ∀ x z : GridState n, z ≠ x →
      (∑ D ∈ (G.hexagonRectangleDecompositions C x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.hexagonRectangleWeight C R D) +
        ∑ D ∈ (G.rectangleHexagonDecompositions C x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.rectangleHexagonWeight C R D =
        ∑ D ∈ G.unpairedHexagonComposites C x z, G.hexagonCompositeWeight C R D :=
    fun x z hzx => by
      rw [← G.sum_hexagonCompositeWeight_filter_not_hasDisjointSides C R,
        G.sum_hexagonCompositeWeight_overlap_eq_sum_unpaired C R hzx]
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x z hzx => ?_⟩
    · simpa only [GridRectangleDecomposition.filter_not_hasDisjointSides_eq_self, eq_self,
        ite_true] using h x x
    · simpa only [hoff x z hzx, ite_eq_right (Ne.symm hzx), zero_add] using h x z
  · rintro ⟨hdiag, hunpaired⟩ x z
    by_cases hzx : z = x
    · subst z
      simpa only [GridRectangleDecomposition.filter_not_hasDisjointSides_eq_self, eq_self,
        ite_true] using hdiag x
    · rw [hoff x z hzx, ite_eq_right (Ne.symm hzx), zero_add]
      exact hunpaired x z hzx

end GridDiagram

end TauCeti
