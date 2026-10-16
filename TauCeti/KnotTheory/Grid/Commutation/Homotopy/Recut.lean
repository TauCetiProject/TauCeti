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

Both orders of composition lie on the same side of the equation, so they are treated here as one
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

## Main definitions

* `TauCeti.GridHexagonCompositeDecomposition`: a commutation hexagon followed by a rectangle, or a
  rectangle followed by a commutation hexagon.
* `TauCeti.GridDiagram.hexagonCompositeDecompositions` and
  `TauCeti.GridDiagram.hexagonCompositeWeight`: the counted composites and their weights.
* `TauCeti.GridDiagram.unpairedHexagonComposites`: the counted composites sharing a side column
  whose recut underlies no counted composite.

## Main results

* `TauCeti.GridDiagram.hexagonCompositeWeight_eq_of_isRepartition`: two counted composites covering
  the same squares have the same weight.
* `TauCeti.GridDiagram.injOn_toRectangleDecomposition_hexagonCompositeDecompositions`: a counted
  composite is determined by its underlying rectangle decomposition.
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

open MvPolynomial

/-- A two-step domain on the left-hand side of the commutation homotopy equation: a commutation
hexagon followed by a rectangle, or a rectangle followed by a commutation hexagon. -/
abbrev GridHexagonCompositeDecomposition {n : ℕ} (a s s' : Fin n) (x z : GridState n) :=
  GridHexagonRectangleDecomposition a s s' x z ⊕ GridRectangleHexagonDecomposition a s s' x z

namespace GridHexagonCompositeDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Forget the turns of the hexagon in a hexagon composite. -/
def toRectangleDecomposition (D : GridHexagonCompositeDecomposition a s s' x z) :
    GridRectangleDecomposition x z :=
  D.elim GridHexagonRectangleDecomposition.toRectangleDecomposition
    GridRectangleHexagonDecomposition.toRectangleDecomposition

/-- The underlying rectangle decomposition of a hexagon followed by a rectangle. -/
@[simp]
theorem toRectangleDecomposition_inl (D : GridHexagonRectangleDecomposition a s s' x z) :
    toRectangleDecomposition (Sum.inl D : GridHexagonCompositeDecomposition a s s' x z) =
      D.toRectangleDecomposition := (rfl)

/-- The underlying rectangle decomposition of a rectangle followed by a hexagon. -/
@[simp]
theorem toRectangleDecomposition_inr (D : GridRectangleHexagonDecomposition a s s' x z) :
    toRectangleDecomposition (Sum.inr D : GridHexagonCompositeDecomposition a s s' x z) =
      D.toRectangleDecomposition := (rfl)

end GridHexagonCompositeDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

variable (R : Type*) [CommSemiring R]

/-! ### The counted hexagon composites -/

/-- The counted hexagon composites from `x` to `z`: the counted hexagon--rectangle and
rectangle--hexagon decompositions. -/
noncomputable def hexagonCompositeDecompositions (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z) :=
  (G.hexagonRectangleDecompositions C x z).disjSum (G.rectangleHexagonDecompositions C x z)

/-- A hexagon followed by a rectangle is a counted composite exactly when it is counted as a
hexagon--rectangle decomposition. -/
@[simp]
theorem inl_mem_hexagonCompositeDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    Sum.inl D ∈ G.hexagonCompositeDecompositions C x z ↔
      D ∈ G.hexagonRectangleDecompositions C x z :=
  Finset.inl_mem_disjSum

/-- A rectangle followed by a hexagon is a counted composite exactly when it is counted as a
rectangle--hexagon decomposition. -/
@[simp]
theorem inr_mem_hexagonCompositeDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    Sum.inr D ∈ G.hexagonCompositeDecompositions C x z ↔
      D ∈ G.rectangleHexagonDecompositions C x z :=
  Finset.inr_mem_disjSum

/-- The weight of a hexagon composite: that of its hexagon--rectangle or rectangle--hexagon
decomposition. -/
noncomputable def hexagonCompositeWeight {x z : GridState n}
    (D : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    MvPolynomial (Fin n) R :=
  D.elim (G.hexagonRectangleWeight C R) (G.rectangleHexagonWeight C R)

/-- The weight of a hexagon followed by a rectangle. -/
@[simp]
theorem hexagonCompositeWeight_inl {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.hexagonCompositeWeight C R (Sum.inl D) = G.hexagonRectangleWeight C R D := (rfl)

/-- The weight of a rectangle followed by a hexagon. -/
@[simp]
theorem hexagonCompositeWeight_inr {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.hexagonCompositeWeight C R (Sum.inr D) = G.rectangleHexagonWeight C R D := (rfl)

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
  simp only [Finset.sum_filter, hexagonCompositeDecompositions, Finset.sum_disjSum,
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
    hexagonCompositeWeight_inl, hexagonCompositeWeight_inr]

/-- Both rectangles under a counted composite are empty. -/
theorem isEmpty_of_mem_hexagonCompositeDecompositions {x z : GridState n}
    {D : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  cases D with
  | inl D =>
    obtain ⟨hP, hr⟩ := (G.mem_hexagonRectangleDecompositions C D).mp
      ((G.inl_mem_hexagonCompositeDecompositions C D).mp hD)
    exact ⟨((G.mem_commutationHexagons C _).mp hP).1, G.isEmpty_of_mem_unblockedRectangles hr⟩
  | inr D =>
    obtain ⟨hr, hP⟩ := (G.mem_rectangleHexagonDecompositions C D).mp
      ((G.inr_mem_hexagonCompositeDecompositions C D).mp hD)
    exact ⟨G.isEmpty_of_mem_unblockedRectangles hr, ((G.mem_commutationHexagons C _).mp hP).1⟩

/-- A counted composite covers exactly one `X`-marking, that of the column its hexagon cuts away,
and its weight times the variable of that column is the product of the weights of its two
underlying rectangles. -/
private theorem exists_X_mul_hexagonCompositeWeight {x z : GridState n}
    {D : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z) :
    ∃ c : Fin n,
      MvPolynomial.X c * G.hexagonCompositeWeight C R D =
          G.OMonomial R D.toRectangleDecomposition.first.toGridRectangle *
            G.OMonomial R D.toRectangleDecomposition.second.toGridRectangle ∧
        G.XSet ∩ (D.toRectangleDecomposition.first.toGridRectangle.coveredSquares ∪
            D.toRectangleDecomposition.second.toGridRectangle.coveredSquares) =
          {(c, G.X c)} := by
  cases D with
  | inl D =>
    obtain ⟨hP, hr⟩ := (G.mem_hexagonRectangleDecompositions C D).mp
      ((G.inl_mem_hexagonCompositeDecompositions C D).mp hD)
    refine ⟨D.hexagon.cutColumn, ?_, ?_⟩
    · rw [hexagonCompositeWeight_inl, hexagonRectangleWeight_def, ← mul_assoc,
        G.X_cutColumn_mul_commutationHexagonWeight C R,
        GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        Finset.inter_union_distrib_left,
        G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm,
        Finset.union_empty]
  | inr D =>
    obtain ⟨hr, hP⟩ := (G.mem_rectangleHexagonDecompositions C D).mp
      ((G.inr_mem_hexagonCompositeDecompositions C D).mp hD)
    refine ⟨D.hexagon.cutColumn, ?_, ?_⟩
    · rw [hexagonCompositeWeight_inr, rectangleHexagonWeight_def, mul_left_comm,
        G.X_cutColumn_mul_commutationHexagonWeight C R,
        GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        Finset.inter_union_distrib_left,
        G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm,
        Finset.empty_union]

/-- Two counted composites whose underlying rectangle decompositions repartition the same squares
have the same weight. -/
theorem hexagonCompositeWeight_eq_of_isRepartition {x z : GridState n}
    {D E : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z)
    (hE : E ∈ G.hexagonCompositeDecompositions C x z)
    (h : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition) :
    G.hexagonCompositeWeight C R D = G.hexagonCompositeWeight C R E := by
  obtain ⟨c, hcw, hcX⟩ := G.exists_X_mul_hexagonCompositeWeight C R hD
  obtain ⟨d, hdw, hdX⟩ := G.exists_X_mul_hexagonCompositeWeight C R hE
  -- Both composites cover the same squares, hence the same single `X`-marking.
  rw [h.coveredSquares_union_eq, hcX, Finset.singleton_inj] at hdX
  rw [← (Prod.mk.inj hdX).1] at hdw
  refine (X_mul_cancel_left_iff (i := c)).mp ?_
  rw [hcw, hdw, h.OMonomial_mul_OMonomial G R]

/-- A counted composite is determined by its underlying rectangle decomposition: the rectangle
under its hexagon covers an `X`-marking, while its counted rectangle covers none. -/
theorem injOn_toRectangleDecomposition_hexagonCompositeDecompositions (x z : GridState n) :
    Set.InjOn GridHexagonCompositeDecomposition.toRectangleDecomposition
      (G.hexagonCompositeDecompositions C x z : Set
        (GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z)) := by
  intro D hD E hE h
  rw [Finset.mem_coe] at hD hE
  -- A counted hexagon and a counted rectangle never have the same underlying squares.
  have hne : ∀ {v v' : GridState n}
      {P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x v}
      {r : GridRectangleBetween x v'}, P ∈ G.commutationHexagons C x v →
      r ∈ G.unblockedRectangles x v' →
      P.toGridRectangleBetween.toGridRectangle.coveredSquares ≠
        r.toGridRectangle.coveredSquares := by
    intro v v' P r hP hr hcov
    have hmem : (P.cutColumn, G.X P.cutColumn) ∈
        G.XSet ∩ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
      rw [G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP]
      exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, hcov] at hmem
    exact Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hmem.2 hmem.1
  cases D with
  | inl D =>
    cases E with
    | inl E =>
      exact congrArg Sum.inl
        (GridHexagonRectangleDecomposition.toRectangleDecomposition_injective h)
    | inr E =>
      exact (hne ((G.mem_hexagonRectangleDecompositions C D).mp
        ((G.inl_mem_hexagonCompositeDecompositions C D).mp hD)).1
        ((G.mem_rectangleHexagonDecompositions C E).mp
          ((G.inr_mem_hexagonCompositeDecompositions C E).mp hE)).1
        (congrArg (fun F : GridRectangleDecomposition x z =>
          F.first.toGridRectangle.coveredSquares) h)).elim
  | inr D =>
    cases E with
    | inl E =>
      exact (hne ((G.mem_hexagonRectangleDecompositions C E).mp
        ((G.inl_mem_hexagonCompositeDecompositions C E).mp hE)).1
        ((G.mem_rectangleHexagonDecompositions C D).mp
          ((G.inr_mem_hexagonCompositeDecompositions C D).mp hD)).1
        (congrArg (fun F : GridRectangleDecomposition x z =>
          F.first.toGridRectangle.coveredSquares) h.symm)).elim
    | inr E =>
      exact congrArg Sum.inr
        (GridRectangleHexagonDecomposition.toRectangleDecomposition_injective h)

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
