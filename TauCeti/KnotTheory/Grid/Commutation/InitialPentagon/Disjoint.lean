/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Disjoint

/-!
# Disjoint-side pairing for initial-side pentagons

A rectangle and an initial-side pentagon with disjoint vertical side pairs can be applied
in either order. Reuse the reordering of their underlying rectangles. It preserves the
pentagon turn point, covered squares, and emptiness. The rectangle's side columns avoid the
replaced line, so its marking conditions and weight transfer to the commuted diagram.

Consequently the two orders of counted disjoint-side domains have equal total monomial
weight. This is the initial-side part of the disjoint contribution to the commutation
chain-map equation. Domains with common sides are not included in this pairing.

The argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Section 5.1, and the existing terminal-side disjoint-domain pairing.
-/

public section

namespace TauCeti

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Apply the initial-side pentagon before the rectangle when their side pairs are disjoint. -/
def commute (D : GridRectangleInitialPentagonDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    GridInitialPentagonRectangleDecomposition a s x z where
  toGridTwoStepDecomposition := D.toGridRectangleDecomposition.commute h
  first_left_eq := by simpa using D.second_left_eq
  first_turn_mem := by
    have heq := congrArg (fun r : GridRectangle n => s ∈ Grid.cIco r.bottom r.top)
      (D.toGridRectangleDecomposition.commute_first_toGridRectangle h)
    simpa only [GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top] using heq.mpr D.second_turn_mem

/-- Reordering initial-side domains is the ordinary reordering of the underlying rectangles. -/
@[simp]
theorem commute_toGridRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toGridRectangleDecomposition = D.toGridRectangleDecomposition.commute h :=
  (rfl)

/-- Reordering preserves disjointness of the two side pairs. -/
theorem hasDisjointSides_commute (D : GridRectangleInitialPentagonDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toGridRectangleDecomposition.HasDisjointSides := by
  rw [D.commute_toGridRectangleDecomposition h]
  exact D.toGridRectangleDecomposition.hasDisjointSides_commute h

/-- Reordering preserves the squares covered by the initial-side pentagon. -/
@[simp]
theorem commute_pentagon_coveredSquares
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).pentagon.coveredSquares = D.pentagon.coveredSquares :=
  GridInitialPentagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _ (by
    have heq := congrArg (fun E : GridRectangleDecomposition x z => E.first.toGridRectangle)
      (D.commute_toGridRectangleDecomposition h)
    simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
      GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween] using
      heq.trans (D.toGridRectangleDecomposition.commute_first_toGridRectangle h))

/-- Reordering leaves the rectangle's toroidal domain unchanged. -/
@[simp]
theorem commute_rectangle_toGridRectangle
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).second.toGridRectangle = D.first.toGridRectangle :=
  D.toGridRectangleDecomposition.commute_second_toGridRectangle h

/-- A disjoint rectangle covers both commuted columns or neither: its endpoints avoid the
replaced line, which is the initial side of the pentagon. -/
theorem rectangle_mem_coveredColumns_iff
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    a ∈ D.first.toGridRectangle.coveredColumns ↔
      finRotate n a ∈ D.first.toGridRectangle.coveredColumns := by
  obtain ⟨hll, _, hrl, _⟩ := D.toGridRectangleDecomposition.hasDisjointSides_iff.mp h
  simp only [GridRectangle.mem_coveredColumns]
  exact (Grid.mem_cIco_finRotate_iff_of_ne
    (D.second_left_eq ▸ hll) (D.second_left_eq ▸ hrl)).symm

end GridRectangleInitialPentagonDecomposition

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Apply the rectangle before the initial-side pentagon when their side pairs are disjoint. -/
def commute (D : GridInitialPentagonRectangleDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    GridRectangleInitialPentagonDecomposition a s x z where
  toGridTwoStepDecomposition := D.toGridRectangleDecomposition.commute h
  second_left_eq := by simpa using D.first_left_eq
  second_turn_mem := by
    have heq := congrArg (fun r : GridRectangle n => s ∈ Grid.cIco r.bottom r.top)
      (D.toGridRectangleDecomposition.commute_second_toGridRectangle h)
    simpa only [GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top] using heq.mpr D.first_turn_mem

/-- Reordering initial-side domains is the ordinary reordering of the underlying rectangles. -/
@[simp]
theorem commute_toGridRectangleDecomposition
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toGridRectangleDecomposition = D.toGridRectangleDecomposition.commute h :=
  (rfl)

/-- Reordering preserves disjointness of the two side pairs. -/
theorem hasDisjointSides_commute (D : GridInitialPentagonRectangleDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toGridRectangleDecomposition.HasDisjointSides := by
  rw [D.commute_toGridRectangleDecomposition h]
  exact D.toGridRectangleDecomposition.hasDisjointSides_commute h

/-- Reordering twice recovers the initial-side pentagon--rectangle decomposition. -/
@[simp]
theorem commute_commute (D : GridInitialPentagonRectangleDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  apply ext
  simp

/-- Reordering preserves the squares covered by the initial-side pentagon. -/
@[simp]
theorem commute_pentagon_coveredSquares
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).pentagon.coveredSquares = D.pentagon.coveredSquares :=
  GridInitialPentagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _ (by
    have heq := congrArg (fun E : GridRectangleDecomposition x z => E.second.toGridRectangle)
      (D.commute_toGridRectangleDecomposition h)
    simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
      GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween] using
      heq.trans (D.toGridRectangleDecomposition.commute_second_toGridRectangle h))

/-- Reordering leaves the rectangle's toroidal domain unchanged. -/
@[simp]
theorem commute_rectangle_toGridRectangle
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).first.toGridRectangle = D.second.toGridRectangle :=
  D.toGridRectangleDecomposition.commute_first_toGridRectangle h

/-- A disjoint rectangle covers both commuted columns or neither. -/
theorem rectangle_mem_coveredColumns_iff
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    a ∈ D.second.toGridRectangle.coveredColumns ↔
      finRotate n a ∈ D.second.toGridRectangle.coveredColumns := by
  obtain ⟨hll, hlr, _, _⟩ := D.toGridRectangleDecomposition.hasDisjointSides_iff.mp h
  simp only [GridRectangle.mem_coveredColumns]
  exact (Grid.mem_cIco_finRotate_iff_of_ne
    (D.first_left_eq ▸ hll.symm) (D.first_left_eq ▸ hlr.symm)).symm

end GridInitialPentagonRectangleDecomposition

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Reordering twice recovers the rectangle--initial-side pentagon decomposition. -/
@[simp]
theorem commute_commute (D : GridRectangleInitialPentagonDecomposition a s x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  apply ext
  simp

end GridRectangleInitialPentagonDecomposition

/-- Reordering is an equivalence between the two orders of initial-side domains with disjoint
vertical side pairs. -/
def initialPentagonDisjointCommuteEquiv {n : ℕ} (a s : Fin n) (x z : GridState n) :
    {D : GridRectangleInitialPentagonDecomposition a s x z //
      D.toGridRectangleDecomposition.HasDisjointSides} ≃
    {D : GridInitialPentagonRectangleDecomposition a s x z //
      D.toGridRectangleDecomposition.HasDisjointSides} where
  toFun D := ⟨D.1.commute D.2, D.1.hasDisjointSides_commute D.2⟩
  invFun D := ⟨D.1.commute D.2, D.1.hasDisjointSides_commute D.2⟩
  left_inv D := Subtype.ext (D.1.commute_commute D.2)
  right_inv D := Subtype.ext (D.1.commute_commute D.2)

/-- The forward equivalence reorders a rectangle followed by an initial-side pentagon. -/
@[simp]
theorem initialPentagonDisjointCommuteEquiv_apply {n : ℕ} (a s : Fin n) (x z : GridState n)
    (D : {D : GridRectangleInitialPentagonDecomposition a s x z //
      D.toGridRectangleDecomposition.HasDisjointSides}) :
    (initialPentagonDisjointCommuteEquiv a s x z D).1 = D.1.commute D.2 :=
  (rfl)

/-- The inverse equivalence reorders an initial-side pentagon followed by a rectangle. -/
@[simp]
theorem initialPentagonDisjointCommuteEquiv_symm_apply {n : ℕ} (a s : Fin n) (x z : GridState n)
    (D : {D : GridInitialPentagonRectangleDecomposition a s x z //
      D.toGridRectangleDecomposition.HasDisjointSides}) :
    ((initialPentagonDisjointCommuteEquiv a s x z).symm D).1 = D.1.commute D.2 :=
  (rfl)

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

/-- Reordering preserves countedness of disjoint rectangle--initial-side pentagon domains. -/
theorem commute_mem_initialPentagonRectangleDecompositions {x z : GridState n}
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.commute h ∈ G.initialPentagonRectangleDecompositions C x z := by
  rw [G.mem_rectangleInitialPentagonDecompositions C D, G.mem_unblockedRectangles,
    G.mem_initialPentagons,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] at hD
  rw [G.mem_initialPentagonRectangleDecompositions C (D.commute h),
    G.mem_initialPentagons,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
    (G.swapColumns C.column b).mem_unblockedRectangles]
  refine ⟨⟨D.toGridRectangleDecomposition.isEmpty_commute_first h hD.1.1 hD.2.1, ?_⟩,
    ⟨D.toGridRectangleDecomposition.isEmpty_commute_second h hD.1.1 hD.2.1, ?_⟩⟩
  · simpa only [D.commute_pentagon_coveredSquares h] using hD.2.2
  · rw [D.commute_rectangle_toGridRectangle h]
    exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns
      D.first.toGridRectangle (D.rectangle_mem_coveredColumns_iff h)).mpr hD.1.2

/-- The reverse reordering preserves countedness of disjoint initial-side pentagon--rectangle
domains. -/
theorem commute_mem_rectangleInitialPentagonDecompositions {x z : GridState n}
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.initialPentagonRectangleDecompositions C x z) :
    D.commute h ∈ G.rectangleInitialPentagonDecompositions C x z := by
  rw [G.mem_initialPentagonRectangleDecompositions C D, G.mem_initialPentagons,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
    (G.swapColumns C.column b).mem_unblockedRectangles] at hD
  rw [G.mem_rectangleInitialPentagonDecompositions C (D.commute h), G.mem_unblockedRectangles,
    G.mem_initialPentagons,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
  refine ⟨⟨D.toGridRectangleDecomposition.isEmpty_commute_first h hD.1.1 hD.2.1, ?_⟩,
    ⟨D.toGridRectangleDecomposition.isEmpty_commute_second h hD.1.1 hD.2.1, ?_⟩⟩
  · rw [D.commute_rectangle_toGridRectangle h]
    exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns
      D.second.toGridRectangle (D.rectangle_mem_coveredColumns_iff h)).mp hD.2.2
  · simpa only [D.commute_pentagon_coveredSquares h] using hD.1.2

variable (R : Type*) [CommSemiring R]

/-- Reordering disjoint initial-side domains preserves the composite monomial weight. -/
theorem initialPentagonRectangleWeight_commute_rectangleInitialPentagon {x z : GridState n}
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    G.initialPentagonRectangleWeight C R (D.commute h) =
      G.rectangleInitialPentagonWeight C R D := by
  have hpentagon : G.initialPentagonWeight R C (D.commute h).pentagon =
      G.initialPentagonWeight R C D.pentagon := by
    rw [G.initialPentagonWeight_eq_prod_coveredSquares R C,
      G.initialPentagonWeight_eq_prod_coveredSquares R C, D.commute_pentagon_coveredSquares h]
  rw [G.initialPentagonRectangleWeight_def C R, G.rectangleInitialPentagonWeight_def C R,
    D.commute_rectangle_toGridRectangle h, hpentagon,
    G.OMonomial_swapColumns_eq_rename_of_coveredColumns R
      D.first.toGridRectangle (D.rectangle_mem_coveredColumns_iff h), mul_comm]

/-- The reverse reordering also preserves the composite monomial weight. -/
theorem rectangleInitialPentagonWeight_commute_initialPentagonRectangle {x z : GridState n}
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : D.toGridRectangleDecomposition.HasDisjointSides) :
    G.rectangleInitialPentagonWeight C R (D.commute h) =
      G.initialPentagonRectangleWeight C R D := by
  have hweight := G.initialPentagonRectangleWeight_commute_rectangleInitialPentagon C R
    (D.commute h) (D.hasDisjointSides_commute h)
  rw [D.commute_commute h] at hweight
  exact hweight.symm

open Classical in
/-- The disjoint-side contributions of initial-side pentagons to the two orders in the
commutation chain-map equation have equal total monomial weight. -/
theorem sum_rectangleInitialPentagonWeight_disjoint_eq_sum_initialPentagonRectangleWeight_disjoint
    (x z : GridState n) :
    ∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
        (fun D => D.toGridRectangleDecomposition.HasDisjointSides),
        G.rectangleInitialPentagonWeight C R D =
      ∑ D ∈ (G.initialPentagonRectangleDecompositions C x z).filter
        (fun D => D.toGridRectangleDecomposition.HasDisjointSides),
        G.initialPentagonRectangleWeight C R D := by
  classical
  let e := initialPentagonDisjointCommuteEquiv C.column C.turnRow x z
  refine Finset.sum_bij'
    (fun D hD => (e ⟨D, (Finset.mem_filter.mp hD).2⟩).1)
    (fun E hE => (e.symm ⟨E, (Finset.mem_filter.mp hE).2⟩).1) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    have h := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr
      ⟨by simpa only [e, initialPentagonDisjointCommuteEquiv_apply] using
          G.commute_mem_initialPentagonRectangleDecompositions C D h.2 h.1,
        (e ⟨D, h.2⟩).2⟩
  · intro E hE
    have h := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr
      ⟨by simpa only [e, initialPentagonDisjointCommuteEquiv_symm_apply] using
          G.commute_mem_rectangleInitialPentagonDecompositions C E h.2 h.1,
        (e.symm ⟨E, h.2⟩).2⟩
  · intro D hD
    exact congrArg Subtype.val (e.left_inv ⟨D, (Finset.mem_filter.mp hD).2⟩)
  · intro E hE
    exact congrArg Subtype.val (e.right_inv ⟨E, (Finset.mem_filter.mp hE).2⟩)
  · intro D hD
    simpa only [e, initialPentagonDisjointCommuteEquiv_apply] using
      (G.initialPentagonRectangleWeight_commute_rectangleInitialPentagon C R D
        (Finset.mem_filter.mp hD).2).symm

end GridDiagram

end TauCeti
