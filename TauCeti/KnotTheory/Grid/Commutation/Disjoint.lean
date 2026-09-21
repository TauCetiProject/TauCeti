/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Disjoint

/-!
# Disjoint domains in the grid commutation map

The chain-map equation for a grid column commutation compares a rectangle followed by a
pentagon with a pentagon followed by a rectangle. When their pairs of vertical sides are
disjoint, the two moves commute. This file constructs that reordering and records how it
preserves the two geometric domains.

The terminal side of every pentagon is the replaced grid line. Consequently a rectangle whose
sides are disjoint from the pentagon has neither endpoint on that line. Swapping the two columns
adjacent to the line therefore preserves the rectangle's covered squares; this is the extra
fact needed to transport the rectangle count from the original diagram to the commuted one.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.commute`: reorder a rectangle and pentagon with
  disjoint side pairs.
* `TauCeti.GridPentagonRectangleDecomposition.commute`: the inverse reordering.
* `TauCeti.GridRectanglePentagonDecomposition.commute_commute`: the two reorderings are inverse.
* `TauCeti.GridDiagram.commute_mem_pentagonRectangleDecompositions`: reordering sends counted
  domains to counted domains.
* `TauCeti.GridDiagram.pentagonRectangleWeight_commute_rectanglePentagon`: reordering preserves
  the monomial weight of a composite domain.

## References

This is the disjoint-domain case of the pentagon--rectangle juxtaposition argument in
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ}

/-- Swapping two cyclically consecutive columns preserves a rectangle's covered squares when
the second column is not a vertical side of the rectangle. -/
theorem mem_coveredSquares_swap_finRotate_iff_of_ne (r : GridRectangle n) {a : Fin n}
    (hleft : r.left ≠ finRotate n a) (hright : r.right ≠ finRotate n a)
    (p : Fin n × Fin n) :
    (Equiv.swap a (finRotate n a) p.1, p.2) ∈ r.coveredSquares ↔
      p ∈ r.coveredSquares := by
  simp only [mem_coveredSquares, mem_coveredColumns, mem_coveredRows]
  rw [Grid.mem_cIco_swap_finRotate_iff_of_ne hleft hright]

/-- Avoidance of the `X`-markings is unchanged by swapping two cyclically consecutive columns
when the second column is not a vertical side of the rectangle. -/
theorem disjoint_coveredSquares_XSet_swapColumns_iff_of_ne (r : GridRectangle n)
    (G : GridDiagram n) {a : Fin n} (hleft : r.left ≠ finRotate n a)
    (hright : r.right ≠ finRotate n a) :
    Disjoint r.coveredSquares (G.swapColumns a (finRotate n a)).XSet ↔
      Disjoint r.coveredSquares G.XSet := by
  rw [Finset.disjoint_left, Finset.disjoint_left]
  constructor
  · intro h p hp hpX
    let q : Fin n × Fin n := (Equiv.swap a (finRotate n a) p.1, p.2)
    apply h
    · exact (r.mem_coveredSquares_swap_finRotate_iff_of_ne hleft hright p).mpr hp
    · rw [G.mem_XSet_swapColumns]
      simpa only [q, Equiv.swap_apply_self] using hpX
  · intro h p hp hpX
    rw [G.mem_XSet_swapColumns] at hpX
    apply h
    · exact (r.mem_coveredSquares_swap_finRotate_iff_of_ne hleft hright p).mpr hp
    · exact hpX

/-- Swapping two cyclically consecutive columns carries the covered `O`-columns of a rectangle
to their images under the same swap, provided the second column is not a rectangle side. -/
theorem OColumns_swapColumns_eq_image_of_ne (r : GridRectangle n) (G : GridDiagram n)
    {a : Fin n} (hleft : r.left ≠ finRotate n a) (hright : r.right ≠ finRotate n a) :
    (G.swapColumns a (finRotate n a)).OColumns r =
      (G.OColumns r).image (Equiv.swap a (finRotate n a)) := by
  ext c
  rw [(G.swapColumns a (finRotate n a)).mem_OColumns, Finset.mem_image]
  simp only [GridDiagram.swapColumns_O, GridState.swapColumns_apply]
  constructor
  · intro hc
    refine ⟨Equiv.swap a (finRotate n a) c, ?_, Equiv.swap_apply_self _ _ _⟩
    rw [G.mem_OColumns]
    exact (r.mem_coveredSquares_swap_finRotate_iff_of_ne hleft hright
      (c, G.O (Equiv.swap a (finRotate n a) c))).mpr hc
  · rintro ⟨d, hd, rfl⟩
    rw [G.mem_OColumns] at hd
    simpa only [Equiv.swap_apply_self] using
      (r.mem_coveredSquares_swap_finRotate_iff_of_ne hleft hright (d, G.O d)).mpr hd

/-- Renaming the variables in a rectangle monomial agrees with swapping two cyclically
consecutive columns of the diagram when the second column is not a rectangle side. -/
theorem rename_OMonomial_eq_swapColumns_of_ne (r : GridRectangle n) (G : GridDiagram n)
    (R : Type*) [CommSemiring R] {a : Fin n} (hleft : r.left ≠ finRotate n a)
    (hright : r.right ≠ finRotate n a) :
    MvPolynomial.rename (Equiv.swap a (finRotate n a)) (G.OMonomial R r) =
      (G.swapColumns a (finRotate n a)).OMonomial R r := by
  rw [G.OMonomial_def R r, (G.swapColumns a (finRotate n a)).OMonomial_def R r,
    r.OColumns_swapColumns_eq_image_of_ne G hleft hright, map_prod]
  simp only [MvPolynomial.rename_X,
    Finset.prod_image (Equiv.swap a (finRotate n a)).injective.injOn]

end GridRectangle

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Forget that the first domain of a pentagon--rectangle decomposition has a distinguished
turn point. -/
def toRectangleDecomposition (D : GridPentagonRectangleDecomposition a s x z) :
    GridRectangleDecomposition x z where
  middle := D.middle
  first := D.pentagon.toGridRectangleBetween
  second := D.rectangle

/-- A pentagon--rectangle decomposition is determined by its underlying pair of rectangles. -/
theorem toRectangleDecomposition_injective :
    Function.Injective
      (toRectangleDecomposition : GridPentagonRectangleDecomposition a s x z → _) := by
  intro D E h
  have hmiddle := congrArg GridRectangleDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle := by
    have hsigma := congrArg (fun K : GridRectangleDecomposition x z =>
      (⟨K.middle, K.second⟩ : Σ y, GridRectangleBetween y z)) h
    exact (Sigma.mk.inj_iff.mp hsigma).2
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s x y) hmiddle) D.pentagon E.pentagon
  exact GridPentagonRectangleDecomposition.ext hmiddle hpentagon hrectangle

/-- The pentagon and rectangle have disjoint pairs of vertical sides. -/
def HasDisjointSides (D : GridPentagonRectangleDecomposition a s x z) : Prop :=
  D.toRectangleDecomposition.HasDisjointSides

/-- Disjointness of a pentagon and rectangle is disjointness of their underlying rectangle
side pairs. -/
theorem hasDisjointSides_iff (D : GridPentagonRectangleDecomposition a s x z) :
    D.HasDisjointSides ↔ D.toRectangleDecomposition.HasDisjointSides :=
  Iff.rfl

end GridPentagonRectangleDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Forget that the second domain of a rectangle--pentagon decomposition has a distinguished
turn point. -/
def toRectangleDecomposition (D : GridRectanglePentagonDecomposition a s x z) :
    GridRectangleDecomposition x z where
  middle := D.middle
  first := D.rectangle
  second := D.pentagon.toGridRectangleBetween

/-- The rectangle and pentagon have disjoint pairs of vertical sides. -/
def HasDisjointSides (D : GridRectanglePentagonDecomposition a s x z) : Prop :=
  D.toRectangleDecomposition.HasDisjointSides

/-- Disjointness of a rectangle and pentagon is disjointness of their underlying rectangle
side pairs. -/
theorem hasDisjointSides_iff (D : GridRectanglePentagonDecomposition a s x z) :
    D.HasDisjointSides ↔ D.toRectangleDecomposition.HasDisjointSides :=
  Iff.rfl

/-- Reorder a rectangle followed by a pentagon when their vertical side pairs are disjoint. -/
def commute (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides) :
    GridPentagonRectangleDecomposition a s x z := by
  let E := D.toRectangleDecomposition.commute h
  have hrect : E.first.toGridRectangle = D.pentagon.toGridRectangle :=
    D.toRectangleDecomposition.commute_first_toGridRectangle h
  exact {
    middle := E.middle
    pentagon := {
      toGridRectangleBetween := E.first
      right_eq := by
        exact D.toRectangleDecomposition.commute_first_right h |>.trans D.pentagon.right_eq
      turn_mem := by
        have hbottom := congrArg GridRectangle.bottom hrect
        have htop := congrArg GridRectangle.top hrect
        simp only [GridRectangleBetween.toGridRectangle_bottom,
          GridRectangleBetween.toGridRectangle_top] at hbottom htop
        have hs : s ∈ Grid.cIco E.first.bottom E.first.top := by
          rw [hbottom, htop]
          exact D.pentagon.turn_mem
        simpa only [GridRectangleBetween.bottom, GridRectangleBetween.top] using hs
    }
    rectangle := E.second
  }

private theorem commute_pentagon_left (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.left = D.pentagon.left :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_first_left h

private theorem commute_pentagon_right (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.right = D.pentagon.right :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_first_right h

private theorem commute_rectangle_left (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.left = D.rectangle.left :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_second_left h

private theorem commute_rectangle_right (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.right = D.rectangle.right :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_second_right h

/-- Forgetting the turn point after reordering gives the ordinary reordering of the two
underlying rectangles. -/
@[simp]
theorem commute_toRectangleDecomposition (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition =
      D.toRectangleDecomposition.commute (D.hasDisjointSides_iff.mp h) := by
  apply GridRectangleDecomposition.ext <;>
    dsimp only [GridPentagonRectangleDecomposition.toRectangleDecomposition,
      toRectangleDecomposition]
  · exact (D.commute_pentagon_left h).trans
      (D.toRectangleDecomposition.commute_first_left _).symm
  · exact (D.commute_pentagon_right h).trans
      (D.toRectangleDecomposition.commute_first_right _).symm
  · exact (D.commute_rectangle_left h).trans
      (D.toRectangleDecomposition.commute_second_left _).symm
  · exact (D.commute_rectangle_right h).trans
      (D.toRectangleDecomposition.commute_second_right _).symm

/-- Reordering preserves disjointness of the two side pairs. -/
theorem hasDisjointSides_commute (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).HasDisjointSides := by
  rw [GridPentagonRectangleDecomposition.hasDisjointSides_iff,
    D.commute_toRectangleDecomposition h]
  exact D.toRectangleDecomposition.hasDisjointSides_commute (D.hasDisjointSides_iff.mp h)

/-- The pentagon after reordering covers the same squares as the original pentagon. -/
@[simp]
theorem commute_pentagon_coveredSquares (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).pentagon.coveredSquares = D.pentagon.coveredSquares := by
  have hrect : (D.commute h).pentagon.toGridRectangle = D.pentagon.toGridRectangle := by
    have hforget := congrArg (fun E : GridRectangleDecomposition x z =>
      E.first.toGridRectangle) (D.commute_toRectangleDecomposition h)
    exact hforget.trans (D.toRectangleDecomposition.commute_first_toGridRectangle
      (D.hasDisjointSides_iff.mp h))
  have hleft := congrArg GridRectangle.left hrect
  have hbottom := congrArg GridRectangle.bottom hrect
  have htop := congrArg GridRectangle.top hrect
  simp only [GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top] at hleft hbottom htop
  ext p
  rw [GridPentagonBetween.mem_coveredSquares, GridPentagonBetween.mem_coveredSquares]
  simp only [hleft, hbottom, htop]

/-- The rectangle after reordering covers the same squares as the original rectangle. -/
@[simp]
theorem commute_rectangle_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides) :
    (D.commute h).rectangle.toGridRectangle = D.rectangle.toGridRectangle := by
  have hrect := D.toRectangleDecomposition.commute_second_toGridRectangle
    (D.hasDisjointSides_iff.mp h)
  exact hrect

private theorem isEmpty_commute_pentagon
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.commute h).pentagon.IsEmpty := by
  unfold commute
  exact D.toRectangleDecomposition.isEmpty_commute_first h hrectangle hpentagon

private theorem isEmpty_commute_rectangle
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.commute h).rectangle.IsEmpty := by
  unfold commute
  exact D.toRectangleDecomposition.isEmpty_commute_second h hrectangle hpentagon

/-- A rectangle--pentagon decomposition is determined by its underlying pair of rectangles. -/
theorem toRectangleDecomposition_injective :
    Function.Injective
      (toRectangleDecomposition : GridRectanglePentagonDecomposition a s x z → _) := by
  intro D E h
  have hmiddle := congrArg GridRectangleDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle := by
    have hsigma := congrArg (fun K : GridRectangleDecomposition x z =>
      (⟨K.middle, K.first⟩ : Σ y, GridRectangleBetween x y)) h
    exact (Sigma.mk.inj_iff.mp hsigma).2
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s y z) hmiddle) D.pentagon E.pentagon
  exact GridRectanglePentagonDecomposition.ext hmiddle hrectangle hpentagon

end GridRectanglePentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Reorder a pentagon followed by a rectangle when their vertical side pairs are disjoint. -/
def commute (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides) :
    GridRectanglePentagonDecomposition a s x z := by
  let E := D.toRectangleDecomposition.commute h
  have hrect : E.second.toGridRectangle = D.pentagon.toGridRectangle :=
    D.toRectangleDecomposition.commute_second_toGridRectangle h
  exact {
    middle := E.middle
    rectangle := E.first
    pentagon := {
      toGridRectangleBetween := E.second
      right_eq := by
        exact D.toRectangleDecomposition.commute_second_right h |>.trans D.pentagon.right_eq
      turn_mem := by
        have hbottom := congrArg GridRectangle.bottom hrect
        have htop := congrArg GridRectangle.top hrect
        simp only [GridRectangleBetween.toGridRectangle_bottom,
          GridRectangleBetween.toGridRectangle_top] at hbottom htop
        have hs : s ∈ Grid.cIco E.second.bottom E.second.top := by
          rw [hbottom, htop]
          exact D.pentagon.turn_mem
        simpa only [GridRectangleBetween.bottom, GridRectangleBetween.top] using hs
    }
  }

private theorem commute_rectangle_left (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.left = D.rectangle.left :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_first_left h

private theorem commute_rectangle_right (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.right = D.rectangle.right :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_first_right h

private theorem commute_pentagon_left (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.left = D.pentagon.left :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_second_left h

private theorem commute_pentagon_right (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.right = D.pentagon.right :=
  by
    unfold commute
    exact D.toRectangleDecomposition.commute_second_right h

/-- Forgetting the turn point after reordering gives the ordinary reordering of the two
underlying rectangles. -/
@[simp]
theorem commute_toRectangleDecomposition (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition =
      D.toRectangleDecomposition.commute (D.hasDisjointSides_iff.mp h) := by
  apply GridRectangleDecomposition.ext <;>
    dsimp only [GridRectanglePentagonDecomposition.toRectangleDecomposition,
      toRectangleDecomposition]
  · exact (D.commute_rectangle_left h).trans
      (D.toRectangleDecomposition.commute_first_left _).symm
  · exact (D.commute_rectangle_right h).trans
      (D.toRectangleDecomposition.commute_first_right _).symm
  · exact (D.commute_pentagon_left h).trans
      (D.toRectangleDecomposition.commute_second_left _).symm
  · exact (D.commute_pentagon_right h).trans
      (D.toRectangleDecomposition.commute_second_right _).symm

/-- Reordering preserves disjointness of the two side pairs. -/
theorem hasDisjointSides_commute (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).HasDisjointSides := by
  rw [GridRectanglePentagonDecomposition.hasDisjointSides_iff,
    D.commute_toRectangleDecomposition h]
  exact D.toRectangleDecomposition.hasDisjointSides_commute (D.hasDisjointSides_iff.mp h)

/-- The pentagon after reordering covers the same squares as the original pentagon. -/
@[simp]
theorem commute_pentagon_coveredSquares (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).pentagon.coveredSquares = D.pentagon.coveredSquares := by
  have hrect : (D.commute h).pentagon.toGridRectangle = D.pentagon.toGridRectangle := by
    have hforget := congrArg (fun E : GridRectangleDecomposition x z =>
      E.second.toGridRectangle) (D.commute_toRectangleDecomposition h)
    exact hforget.trans (D.toRectangleDecomposition.commute_second_toGridRectangle
      (D.hasDisjointSides_iff.mp h))
  have hleft := congrArg GridRectangle.left hrect
  have hbottom := congrArg GridRectangle.bottom hrect
  have htop := congrArg GridRectangle.top hrect
  simp only [GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top] at hleft hbottom htop
  ext p
  rw [GridPentagonBetween.mem_coveredSquares, GridPentagonBetween.mem_coveredSquares]
  simp only [hleft, hbottom, htop]

/-- The rectangle after reordering covers the same squares as the original rectangle. -/
@[simp]
theorem commute_rectangle_toGridRectangle
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides) :
    (D.commute h).rectangle.toGridRectangle = D.rectangle.toGridRectangle := by
  have hrect := D.toRectangleDecomposition.commute_first_toGridRectangle
    (D.hasDisjointSides_iff.mp h)
  exact hrect

private theorem isEmpty_commute_rectangle
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides)
    (hpentagon : D.pentagon.IsEmpty) (hrectangle : D.rectangle.IsEmpty) :
    (D.commute h).rectangle.IsEmpty := by
  unfold commute
  exact D.toRectangleDecomposition.isEmpty_commute_first h hpentagon hrectangle

private theorem isEmpty_commute_pentagon
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides)
    (hpentagon : D.pentagon.IsEmpty) (hrectangle : D.rectangle.IsEmpty) :
    (D.commute h).pentagon.IsEmpty := by
  unfold commute
  exact D.toRectangleDecomposition.isEmpty_commute_second h hpentagon hrectangle

/-- Reordering a disjoint pentagon--rectangle decomposition twice recovers the original
decomposition. -/
@[simp]
theorem commute_commute (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  apply toRectangleDecomposition_injective
  apply GridRectangleDecomposition.ext <;>
    dsimp only [toRectangleDecomposition]
  · exact (GridRectanglePentagonDecomposition.commute_pentagon_left _ _).trans
      (D.commute_pentagon_left h)
  · exact (GridRectanglePentagonDecomposition.commute_pentagon_right _ _).trans
      (D.commute_pentagon_right h)
  · exact (GridRectanglePentagonDecomposition.commute_rectangle_left _ _).trans
      (D.commute_rectangle_left h)
  · exact (GridRectanglePentagonDecomposition.commute_rectangle_right _ _).trans
      (D.commute_rectangle_right h)

end GridPentagonRectangleDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Reordering a disjoint rectangle--pentagon decomposition twice recovers the original
decomposition. -/
@[simp]
theorem commute_commute (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  apply toRectangleDecomposition_injective
  apply GridRectangleDecomposition.ext <;>
    dsimp only [toRectangleDecomposition]
  · exact (GridPentagonRectangleDecomposition.commute_rectangle_left _ _).trans
      (D.commute_rectangle_left h)
  · exact (GridPentagonRectangleDecomposition.commute_rectangle_right _ _).trans
      (D.commute_rectangle_right h)
  · exact (GridPentagonRectangleDecomposition.commute_pentagon_left _ _).trans
      (D.commute_pentagon_left h)
  · exact (GridPentagonRectangleDecomposition.commute_pentagon_right _ _).trans
      (D.commute_pentagon_right h)

end GridRectanglePentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

/-- Reordering a counted rectangle--pentagon decomposition with disjoint side pairs produces a
counted pentagon--rectangle decomposition. -/
theorem commute_mem_pentagonRectangleDecompositions {x z : GridState n}
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (h : D.HasDisjointSides) (hD : D ∈ G.rectanglePentagonDecompositions C x z) :
    D.commute h ∈ G.pentagonRectangleDecompositions C x z := by
  rw [G.mem_rectanglePentagonDecompositions C D] at hD
  rw [G.mem_pentagonRectangleDecompositions C (D.commute h)]
  rw [G.mem_unblockedRectangles] at hD
  rw [G.mem_pentagons] at hD
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.toRectangleDecomposition.hasDisjointSides_iff.mp
    (D.hasDisjointSides_iff.mp h)
  have hleft : D.rectangle.left ≠ b := by
    rw [← D.pentagon.right_eq]
    exact hlr
  have hright : D.rectangle.right ≠ b := by
    rw [← D.pentagon.right_eq]
    exact hrr
  refine ⟨?_, ?_⟩
  · rw [G.mem_pentagons]
    refine ⟨D.isEmpty_commute_pentagon h hD.1.1 hD.2.1, ?_⟩
    rw [D.commute_pentagon_coveredSquares h]
    exact hD.2.2
  · rw [(G.swapColumns C.column b).mem_unblockedRectangles]
    refine ⟨D.isEmpty_commute_rectangle h hD.1.1 hD.2.1, ?_⟩
    rw [D.commute_rectangle_toGridRectangle h]
    exact (D.rectangle.toGridRectangle.disjoint_coveredSquares_XSet_swapColumns_iff_of_ne G
      (by simpa using hleft) (by simpa using hright)).mpr hD.1.2

/-- Reordering a counted pentagon--rectangle decomposition with disjoint side pairs produces a
counted rectangle--pentagon decomposition. -/
theorem commute_mem_rectanglePentagonDecompositions {x z : GridState n}
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : D.HasDisjointSides) (hD : D ∈ G.pentagonRectangleDecompositions C x z) :
    D.commute h ∈ G.rectanglePentagonDecompositions C x z := by
  rw [G.mem_pentagonRectangleDecompositions C D] at hD
  rw [G.mem_rectanglePentagonDecompositions C (D.commute h)]
  rw [G.mem_pentagons] at hD
  rw [(G.swapColumns C.column b).mem_unblockedRectangles] at hD
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.toRectangleDecomposition.hasDisjointSides_iff.mp
    (D.hasDisjointSides_iff.mp h)
  have hleft : D.rectangle.left ≠ b := by
    rw [← D.pentagon.right_eq]
    exact hrl.symm
  have hright : D.rectangle.right ≠ b := by
    rw [← D.pentagon.right_eq]
    exact hrr.symm
  refine ⟨?_, ?_⟩
  · rw [G.mem_unblockedRectangles]
    refine ⟨D.isEmpty_commute_rectangle h hD.1.1 hD.2.1, ?_⟩
    rw [D.commute_rectangle_toGridRectangle h]
    exact (D.rectangle.toGridRectangle.disjoint_coveredSquares_XSet_swapColumns_iff_of_ne G
      (by simpa using hleft) (by simpa using hright)).mp hD.2.2
  · rw [G.mem_pentagons]
    refine ⟨D.isEmpty_commute_pentagon h hD.1.1 hD.2.1, ?_⟩
    rw [D.commute_pentagon_coveredSquares h]
    exact hD.1.2

variable (R : Type*) [CommSemiring R]

/-- Reordering a rectangle--pentagon decomposition with disjoint side pairs preserves its
weight in the commutation chain-map equation. -/
theorem pentagonRectangleWeight_commute_rectanglePentagon {x z : GridState n}
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (h : D.HasDisjointSides) :
    G.pentagonRectangleWeight C R (D.commute h) =
      G.rectanglePentagonWeight C R D := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.toRectangleDecomposition.hasDisjointSides_iff.mp
    (D.hasDisjointSides_iff.mp h)
  have hleft : D.rectangle.left ≠ b := by
    rw [← D.pentagon.right_eq]
    exact hlr
  have hright : D.rectangle.right ≠ b := by
    rw [← D.pentagon.right_eq]
    exact hrr
  rw [G.pentagonRectangleWeight_def C R, G.rectanglePentagonWeight_def C R,
    D.commute_rectangle_toGridRectangle h]
  have hpentagon : G.pentagonWeight R C (D.commute h).pentagon =
      G.pentagonWeight R C D.pentagon := by
    rw [G.pentagonWeight_eq_prod_coveredSquares R C,
      G.pentagonWeight_eq_prod_coveredSquares R C, D.commute_pentagon_coveredSquares h]
  rw [hpentagon, D.rectangle.toGridRectangle.rename_OMonomial_eq_swapColumns_of_ne G R
    (by simpa using hleft) (by simpa using hright), mul_comm]

/-- Reordering a pentagon--rectangle decomposition with disjoint side pairs preserves its
weight in the commutation chain-map equation. -/
theorem rectanglePentagonWeight_commute_pentagonRectangle {x z : GridState n}
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : D.HasDisjointSides) :
    G.rectanglePentagonWeight C R (D.commute h) =
      G.pentagonRectangleWeight C R D := by
  have hweight := G.pentagonRectangleWeight_commute_rectanglePentagon C R (D.commute h)
    (D.hasDisjointSides_commute h)
  rw [D.commute_commute h] at hweight
  exact hweight.symm

end GridDiagram

end TauCeti
