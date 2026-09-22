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
* `TauCeti.GridRectanglePentagonDecomposition.commute_commute` and
  `TauCeti.GridPentagonRectangleDecomposition.commute_commute`: the two reorderings are inverse.
* `TauCeti.GridDiagram.commute_mem_pentagonRectangleDecompositions`: reordering sends counted
  domains to counted domains.
* `TauCeti.GridDiagram.commute_mem_rectanglePentagonDecompositions`: the reverse reordering sends
  counted domains to counted domains.
* `TauCeti.GridDiagram.pentagonRectangleWeight_commute_rectanglePentagon`: reordering preserves
  the monomial weight of a composite domain.
* `TauCeti.GridDiagram.rectanglePentagonWeight_commute_pentagonRectangle`: weight preservation in
  the reverse direction.

## References

This is the disjoint-domain case of the pentagon--rectangle juxtaposition argument in
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

private theorem rectangleDecomposition_fields_heq {n : ℕ} {x z : GridState n}
    {D E : GridRectangleDecomposition x z} (h : D = E) :
    HEq D.first E.first ∧ HEq D.second E.second := by
  subst E
  exact ⟨HEq.rfl, HEq.rfl⟩

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Forget that the first domain of a pentagon--rectangle decomposition has a distinguished
turn point. -/
def toRectangleDecomposition (D : GridPentagonRectangleDecomposition a s x z) :
    GridRectangleDecomposition x z where
  middle := D.middle
  first := D.pentagon.toGridRectangleBetween
  second := D.rectangle

/-- Forgetting the pentagon turn point preserves the intermediate state. -/
@[simp]
theorem toRectangleDecomposition_middle (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.middle = D.middle := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying rectangle has the pentagon's initial side. -/
@[simp]
theorem toRectangleDecomposition_first_left (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.first.left = D.pentagon.left := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying rectangle has the pentagon's terminal side. -/
@[simp]
theorem toRectangleDecomposition_first_right (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.first.right = D.pentagon.right := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying toroidal rectangle is the pentagon's underlying rectangle. -/
@[simp]
theorem toRectangleDecomposition_first_toGridRectangle
    (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.first.toGridRectangle = D.pentagon.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the rectangle's initial side. -/
@[simp]
theorem toRectangleDecomposition_second_left (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.second.left = D.rectangle.left := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the rectangle's terminal side. -/
@[simp]
theorem toRectangleDecomposition_second_right (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.second.right = D.rectangle.right := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying toroidal rectangle is the decomposition's rectangle. -/
@[simp]
theorem toRectangleDecomposition_second_toGridRectangle
    (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.second.toGridRectangle = D.rectangle.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- A pentagon--rectangle decomposition is determined by its underlying pair of rectangles. -/
theorem toRectangleDecomposition_injective :
    Function.Injective
      (toRectangleDecomposition : GridPentagonRectangleDecomposition a s x z → _) := by
  intro D E h
  have hmiddle := congrArg GridRectangleDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle :=
    (rectangleDecomposition_fields_heq h).2
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s x y) hmiddle) D.pentagon E.pentagon
  exact GridPentagonRectangleDecomposition.ext hmiddle hpentagon hrectangle

/-- The pentagon and rectangle have disjoint pairs of vertical sides. -/
def HasDisjointSides (D : GridPentagonRectangleDecomposition a s x z) : Prop :=
  D.toRectangleDecomposition.HasDisjointSides

/-- Disjointness is definitionally inherited from the underlying rectangle decomposition. -/
theorem hasDisjointSides_def (D : GridPentagonRectangleDecomposition a s x z) :
    D.HasDisjointSides ↔ D.toRectangleDecomposition.HasDisjointSides :=
  Iff.rfl

/-- Disjointness of a pentagon and rectangle, expanded into the four cross-inequalities. -/
theorem hasDisjointSides_iff (D : GridPentagonRectangleDecomposition a s x z) :
    D.HasDisjointSides ↔
      D.pentagon.left ≠ D.rectangle.left ∧ D.pentagon.left ≠ D.rectangle.right ∧
        D.pentagon.right ≠ D.rectangle.left ∧ D.pentagon.right ≠ D.rectangle.right :=
  by
    rw [hasDisjointSides_def, D.toRectangleDecomposition.hasDisjointSides_iff]
    simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_left, toRectangleDecomposition_second_right]

/-- Disjointness puts the initial side of the rectangle off the replaced grid line, which is the
terminal side of the pentagon. -/
theorem rectangle_left_ne (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : D.rectangle.left ≠ finRotate n a := by
  rw [← D.pentagon.right_eq]
  exact (D.hasDisjointSides_iff.mp h).2.2.1.symm

/-- Disjointness puts the terminal side of the rectangle off the replaced grid line, which is the
terminal side of the pentagon. -/
theorem rectangle_right_ne (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : D.rectangle.right ≠ finRotate n a := by
  rw [← D.pentagon.right_eq]
  exact (D.hasDisjointSides_iff.mp h).2.2.2.symm

/-- Disjointness makes the rectangle cover the commuted column exactly when it covers the
replaced grid line: neither is one of its sides, and they are cyclically consecutive. -/
theorem rectangle_mem_coveredColumns_iff (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    a ∈ D.rectangle.toGridRectangle.coveredColumns ↔
      finRotate n a ∈ D.rectangle.toGridRectangle.coveredColumns := by
  simp only [GridRectangle.mem_coveredColumns]
  exact (Grid.mem_cIco_finRotate_iff_of_ne (by simpa using D.rectangle_left_ne h)
    (by simpa using D.rectangle_right_ne h)).symm

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

/-- Forgetting the pentagon turn point preserves the intermediate state. -/
@[simp]
theorem toRectangleDecomposition_middle (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.middle = D.middle := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying rectangle has the rectangle's initial side. -/
@[simp]
theorem toRectangleDecomposition_first_left (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.first.left = D.rectangle.left := by
  unfold toRectangleDecomposition
  rfl

/-- Emptiness of the rectangle is preserved when forgetting the pentagon turn point. -/
theorem isEmpty_toRectangleDecomposition_first (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.rectangle.IsEmpty) : D.toRectangleDecomposition.first.IsEmpty := by
  cases D with
  | mk middle rectangle pentagon =>
      unfold toRectangleDecomposition
      exact h

/-- Emptiness of the pentagon's underlying rectangle is preserved when forgetting its turn row. -/
theorem isEmpty_toRectangleDecomposition_second
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.second.IsEmpty := by
  cases D with
  | mk middle rectangle pentagon =>
      unfold toRectangleDecomposition
      exact h

/-- The pentagon's turn row lies between the sides of the second forgotten rectangle. -/
theorem turn_mem_toRectangleDecomposition_second
    (D : GridRectanglePentagonDecomposition a s x z) :
    s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
      D.toRectangleDecomposition.second.top := by
  cases D with
  | mk middle rectangle pentagon =>
      unfold toRectangleDecomposition
      exact pentagon.turn_mem

/-- The first underlying rectangle has the rectangle's terminal side. -/
@[simp]
theorem toRectangleDecomposition_first_right (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.first.right = D.rectangle.right := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying toroidal rectangle is the decomposition's rectangle. -/
@[simp]
theorem toRectangleDecomposition_first_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.first.toGridRectangle = D.rectangle.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the pentagon's initial side. -/
@[simp]
theorem toRectangleDecomposition_second_left (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.second.left = D.pentagon.left := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the pentagon's terminal side. -/
@[simp]
theorem toRectangleDecomposition_second_right (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.second.right = D.pentagon.right := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying toroidal rectangle is the pentagon's underlying rectangle. -/
@[simp]
theorem toRectangleDecomposition_second_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.second.toGridRectangle = D.pentagon.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- The rectangle and pentagon have disjoint pairs of vertical sides. -/
def HasDisjointSides (D : GridRectanglePentagonDecomposition a s x z) : Prop :=
  D.toRectangleDecomposition.HasDisjointSides

/-- Disjointness is definitionally inherited from the underlying rectangle decomposition. -/
theorem hasDisjointSides_def (D : GridRectanglePentagonDecomposition a s x z) :
    D.HasDisjointSides ↔ D.toRectangleDecomposition.HasDisjointSides :=
  Iff.rfl

/-- Disjointness of a rectangle and pentagon, expanded into the four cross-inequalities. -/
theorem hasDisjointSides_iff (D : GridRectanglePentagonDecomposition a s x z) :
    D.HasDisjointSides ↔
      D.rectangle.left ≠ D.pentagon.left ∧ D.rectangle.left ≠ D.pentagon.right ∧
        D.rectangle.right ≠ D.pentagon.left ∧ D.rectangle.right ≠ D.pentagon.right :=
  by
    rw [hasDisjointSides_def, D.toRectangleDecomposition.hasDisjointSides_iff]
    simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_left, toRectangleDecomposition_second_right]

/-- Disjointness puts the initial side of the rectangle off the replaced grid line, which is the
terminal side of the pentagon. -/
theorem rectangle_left_ne (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : D.rectangle.left ≠ finRotate n a := by
  rw [← D.pentagon.right_eq]
  exact (D.hasDisjointSides_iff.mp h).2.1

/-- Disjointness puts the terminal side of the rectangle off the replaced grid line, which is the
terminal side of the pentagon. -/
theorem rectangle_right_ne (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : D.rectangle.right ≠ finRotate n a := by
  rw [← D.pentagon.right_eq]
  exact (D.hasDisjointSides_iff.mp h).2.2.2

/-- Disjointness makes the rectangle cover the commuted column exactly when it covers the
replaced grid line: neither is one of its sides, and they are cyclically consecutive. -/
theorem rectangle_mem_coveredColumns_iff (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    a ∈ D.rectangle.toGridRectangle.coveredColumns ↔
      finRotate n a ∈ D.rectangle.toGridRectangle.coveredColumns := by
  simp only [GridRectangle.mem_coveredColumns]
  exact (Grid.mem_cIco_finRotate_iff_of_ne (by simpa using D.rectangle_left_ne h)
    (by simpa using D.rectangle_right_ne h)).symm

/-- Reorder a rectangle followed by a pentagon when their vertical side pairs are disjoint. -/
def commute (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides) :
    GridPentagonRectangleDecomposition a s x z where
  middle := (D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h)).middle
  pentagon := GridPentagonBetween.ofToGridRectangleEq
    (D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h)).first D.pentagon
      ((D.toRectangleDecomposition.commute_first_toGridRectangle
        (D.hasDisjointSides_def.mp h)).trans D.toRectangleDecomposition_second_toGridRectangle)
  rectangle := (D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h)).second

/-- Forgetting the turn point after reordering gives the ordinary reordering of the two
underlying rectangles. -/
@[simp]
theorem commute_toRectangleDecomposition (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition =
      D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h) := by
  apply GridRectangleDecomposition.ext
  · simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      commute, GridPentagonBetween.ofToGridRectangleEq_toGridRectangleBetween,
      GridRectangleDecomposition.commute_first_left, toRectangleDecomposition_second_left]
  · simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
      commute, GridPentagonBetween.ofToGridRectangleEq_toGridRectangleBetween,
      GridRectangleDecomposition.commute_first_right, toRectangleDecomposition_second_right]
  · simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      commute, GridRectangleDecomposition.commute_second_left,
      toRectangleDecomposition_first_left]
  · simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right,
      commute, GridRectangleDecomposition.commute_second_right,
      toRectangleDecomposition_first_right]

/-- The initial side of the reordered pentagon. -/
@[simp]
theorem commute_pentagon_left (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.left = D.pentagon.left := by
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
    GridRectangleDecomposition.commute_first_left, toRectangleDecomposition_second_left] using
    congrArg (fun E : GridRectangleDecomposition x z => E.first.left)
      (D.commute_toRectangleDecomposition h)

/-- The terminal side of the reordered pentagon. -/
@[simp]
theorem commute_pentagon_right (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.right = D.pentagon.right := by
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
    GridRectangleDecomposition.commute_first_right, toRectangleDecomposition_second_right] using
    congrArg (fun E : GridRectangleDecomposition x z => E.first.right)
      (D.commute_toRectangleDecomposition h)

/-- The initial side of the reordered rectangle. -/
@[simp]
theorem commute_rectangle_left (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.left = D.rectangle.left := by
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
    GridRectangleDecomposition.commute_second_left, toRectangleDecomposition_first_left] using
    congrArg (fun E : GridRectangleDecomposition x z => E.second.left)
      (D.commute_toRectangleDecomposition h)

/-- The terminal side of the reordered rectangle. -/
@[simp]
theorem commute_rectangle_right (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.right = D.rectangle.right := by
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right,
    GridRectangleDecomposition.commute_second_right, toRectangleDecomposition_first_right] using
    congrArg (fun E : GridRectangleDecomposition x z => E.second.right)
      (D.commute_toRectangleDecomposition h)

/-- The intermediate state after reordering. -/
@[simp]
theorem commute_middle (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).middle = x.swapColumns D.pentagon.left D.pentagon.right := by
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
    GridRectangleDecomposition.commute_middle, toRectangleDecomposition_second_left,
    toRectangleDecomposition_second_right] using
    congrArg GridRectangleDecomposition.middle (D.commute_toRectangleDecomposition h)

/-- Reordering preserves disjointness of the two side pairs. -/
theorem hasDisjointSides_commute (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).HasDisjointSides := by
  rw [GridPentagonRectangleDecomposition.hasDisjointSides_def,
    D.commute_toRectangleDecomposition h]
  exact D.toRectangleDecomposition.hasDisjointSides_commute (D.hasDisjointSides_def.mp h)

/-- Reordering leaves the underlying toroidal rectangle of the pentagon unchanged. -/
@[simp]
theorem commute_pentagon_toGridRectangle (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).pentagon.toGridRectangle = D.pentagon.toGridRectangle := by
  have hforget := congrArg (fun E : GridRectangleDecomposition x z =>
    E.first.toGridRectangle) (D.commute_toRectangleDecomposition h)
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using
    hforget.trans (D.toRectangleDecomposition.commute_first_toGridRectangle
      (D.hasDisjointSides_def.mp h))

/-- The pentagon after reordering covers the same squares as the original pentagon. -/
@[simp]
theorem commute_pentagon_coveredSquares (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).pentagon.coveredSquares = D.pentagon.coveredSquares :=
  GridPentagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _
    (D.commute_pentagon_toGridRectangle h)

/-- Reordering leaves the underlying toroidal rectangle unchanged. -/
@[simp]
theorem commute_rectangle_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides) :
    (D.commute h).rectangle.toGridRectangle = D.rectangle.toGridRectangle := by
  have hforget := congrArg (fun E : GridRectangleDecomposition x z =>
    E.second.toGridRectangle) (D.commute_toRectangleDecomposition h)
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle] using
    hforget.trans (D.toRectangleDecomposition.commute_second_toGridRectangle
      (D.hasDisjointSides_def.mp h))

/-- Reordering preserves emptiness of the pentagon when both original domains are empty. -/
theorem isEmpty_commute_pentagon
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.commute h).pentagon.IsEmpty := by
  unfold commute
  simp only [GridPentagonBetween.ofToGridRectangleEq_toGridRectangleBetween]
  exact D.toRectangleDecomposition.isEmpty_commute_first (D.hasDisjointSides_def.mp h)
    hrectangle hpentagon

/-- Reordering preserves emptiness of the rectangle when both original domains are empty. -/
theorem isEmpty_commute_rectangle
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.HasDisjointSides)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.commute h).rectangle.IsEmpty := by
  unfold commute
  exact D.toRectangleDecomposition.isEmpty_commute_second (D.hasDisjointSides_def.mp h)
    hrectangle hpentagon

/-- A rectangle--pentagon decomposition is determined by its underlying pair of rectangles. -/
theorem toRectangleDecomposition_injective :
    Function.Injective
      (toRectangleDecomposition : GridRectanglePentagonDecomposition a s x z → _) := by
  intro D E h
  have hmiddle := congrArg GridRectangleDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle :=
    (rectangleDecomposition_fields_heq h).1
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s y z) hmiddle) D.pentagon E.pentagon
  exact GridRectanglePentagonDecomposition.ext hmiddle hrectangle hpentagon

end GridRectanglePentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Reorder a pentagon followed by a rectangle when their vertical side pairs are disjoint. -/
def commute (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides) :
    GridRectanglePentagonDecomposition a s x z where
  middle := (D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h)).middle
  rectangle := (D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h)).first
  pentagon := GridPentagonBetween.ofToGridRectangleEq
    (D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h)).second D.pentagon
      ((D.toRectangleDecomposition.commute_second_toGridRectangle
        (D.hasDisjointSides_def.mp h)).trans D.toRectangleDecomposition_first_toGridRectangle)

/-- Forgetting the turn point after reordering gives the ordinary reordering of the two
underlying rectangles. -/
@[simp]
theorem commute_toRectangleDecomposition (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition =
      D.toRectangleDecomposition.commute (D.hasDisjointSides_def.mp h) := by
  apply GridRectangleDecomposition.ext
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      commute, GridRectangleDecomposition.commute_first_left,
      toRectangleDecomposition_second_left]
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
      commute, GridRectangleDecomposition.commute_first_right,
      toRectangleDecomposition_second_right]
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
      commute, GridPentagonBetween.ofToGridRectangleEq_toGridRectangleBetween,
      GridRectangleDecomposition.commute_second_left, toRectangleDecomposition_first_left]
  · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      commute, GridPentagonBetween.ofToGridRectangleEq_toGridRectangleBetween,
      GridRectangleDecomposition.commute_second_right, toRectangleDecomposition_first_right]

/-- The initial side of the reordered rectangle. -/
@[simp]
theorem commute_rectangle_left (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.left = D.rectangle.left := by
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
    GridRectangleDecomposition.commute_first_left, toRectangleDecomposition_second_left] using
    congrArg (fun E : GridRectangleDecomposition x z => E.first.left)
      (D.commute_toRectangleDecomposition h)

/-- The terminal side of the reordered rectangle. -/
@[simp]
theorem commute_rectangle_right (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).rectangle.right = D.rectangle.right := by
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
    GridRectangleDecomposition.commute_first_right, toRectangleDecomposition_second_right] using
    congrArg (fun E : GridRectangleDecomposition x z => E.first.right)
      (D.commute_toRectangleDecomposition h)

/-- The initial side of the reordered pentagon. -/
@[simp]
theorem commute_pentagon_left (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.left = D.pentagon.left := by
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
    GridRectangleDecomposition.commute_second_left, toRectangleDecomposition_first_left] using
    congrArg (fun E : GridRectangleDecomposition x z => E.second.left)
      (D.commute_toRectangleDecomposition h)

/-- The terminal side of the reordered pentagon. -/
@[simp]
theorem commute_pentagon_right (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).pentagon.right = D.pentagon.right := by
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
    GridRectangleDecomposition.commute_second_right, toRectangleDecomposition_first_right] using
    congrArg (fun E : GridRectangleDecomposition x z => E.second.right)
      (D.commute_toRectangleDecomposition h)

/-- The intermediate state after reordering. -/
@[simp]
theorem commute_middle (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).middle = x.swapColumns D.rectangle.left D.rectangle.right := by
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_middle,
    GridRectangleDecomposition.commute_middle, toRectangleDecomposition_second_left,
    toRectangleDecomposition_second_right] using
    congrArg GridRectangleDecomposition.middle (D.commute_toRectangleDecomposition h)

/-- Reordering preserves disjointness of the two side pairs. -/
theorem hasDisjointSides_commute (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) : (D.commute h).HasDisjointSides := by
  rw [GridRectanglePentagonDecomposition.hasDisjointSides_def,
    D.commute_toRectangleDecomposition h]
  exact D.toRectangleDecomposition.hasDisjointSides_commute (D.hasDisjointSides_def.mp h)

/-- Reordering leaves the underlying toroidal rectangle of the pentagon unchanged. -/
@[simp]
theorem commute_pentagon_toGridRectangle (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).pentagon.toGridRectangle = D.pentagon.toGridRectangle := by
  have hforget := congrArg (fun E : GridRectangleDecomposition x z =>
    E.second.toGridRectangle) (D.commute_toRectangleDecomposition h)
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle] using
    hforget.trans (D.toRectangleDecomposition.commute_second_toGridRectangle
      (D.hasDisjointSides_def.mp h))

/-- The pentagon after reordering covers the same squares as the original pentagon. -/
@[simp]
theorem commute_pentagon_coveredSquares (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).pentagon.coveredSquares = D.pentagon.coveredSquares :=
  GridPentagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _
    (D.commute_pentagon_toGridRectangle h)

/-- Reordering leaves the underlying toroidal rectangle unchanged. -/
@[simp]
theorem commute_rectangle_toGridRectangle
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides) :
    (D.commute h).rectangle.toGridRectangle = D.rectangle.toGridRectangle := by
  have hforget := congrArg (fun E : GridRectangleDecomposition x z =>
    E.first.toGridRectangle) (D.commute_toRectangleDecomposition h)
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle] using
    hforget.trans (D.toRectangleDecomposition.commute_first_toGridRectangle
      (D.hasDisjointSides_def.mp h))

/-- Reordering preserves emptiness of the rectangle when both original domains are empty. -/
theorem isEmpty_commute_rectangle
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides)
    (hpentagon : D.pentagon.IsEmpty) (hrectangle : D.rectangle.IsEmpty) :
    (D.commute h).rectangle.IsEmpty := by
  unfold commute
  exact D.toRectangleDecomposition.isEmpty_commute_first (D.hasDisjointSides_def.mp h)
    hpentagon hrectangle

/-- Reordering preserves emptiness of the pentagon when both original domains are empty. -/
theorem isEmpty_commute_pentagon
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.HasDisjointSides)
    (hpentagon : D.pentagon.IsEmpty) (hrectangle : D.rectangle.IsEmpty) :
    (D.commute h).pentagon.IsEmpty := by
  unfold commute
  simp only [GridPentagonBetween.ofToGridRectangleEq_toGridRectangleBetween]
  exact D.toRectangleDecomposition.isEmpty_commute_second (D.hasDisjointSides_def.mp h)
    hpentagon hrectangle

/-- Reordering a disjoint pentagon--rectangle decomposition twice recovers the original
decomposition. -/
@[simp]
theorem commute_commute (D : GridPentagonRectangleDecomposition a s x z)
    (h : D.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  apply toRectangleDecomposition_injective
  simpa only [GridRectanglePentagonDecomposition.commute_toRectangleDecomposition,
    commute_toRectangleDecomposition] using
    GridRectangleDecomposition.commute_commute D.toRectangleDecomposition
      (D.hasDisjointSides_def.mp h)

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
  simpa only [GridPentagonRectangleDecomposition.commute_toRectangleDecomposition,
    commute_toRectangleDecomposition] using
    GridRectangleDecomposition.commute_commute D.toRectangleDecomposition
      (D.hasDisjointSides_def.mp h)

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
  refine ⟨?_, ?_⟩
  · rw [G.mem_pentagons]
    refine ⟨D.isEmpty_commute_pentagon h hD.1.1 hD.2.1, ?_⟩
    rw [D.commute_pentagon_coveredSquares h]
    exact hD.2.2
  · rw [(G.swapColumns C.column b).mem_unblockedRectangles]
    refine ⟨D.isEmpty_commute_rectangle h hD.1.1 hD.2.1, ?_⟩
    rw [D.commute_rectangle_toGridRectangle h]
    exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns
      D.rectangle.toGridRectangle (D.rectangle_mem_coveredColumns_iff h)).mpr hD.1.2

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
  refine ⟨?_, ?_⟩
  · rw [G.mem_unblockedRectangles]
    refine ⟨D.isEmpty_commute_rectangle h hD.1.1 hD.2.1, ?_⟩
    rw [D.commute_rectangle_toGridRectangle h]
    exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns
      D.rectangle.toGridRectangle (D.rectangle_mem_coveredColumns_iff h)).mp hD.2.2
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
  rw [G.pentagonRectangleWeight_def C R, G.rectanglePentagonWeight_def C R,
    D.commute_rectangle_toGridRectangle h]
  have hpentagon : G.pentagonWeight R C (D.commute h).pentagon =
      G.pentagonWeight R C D.pentagon := by
    rw [G.pentagonWeight_eq_prod_coveredSquares R C,
      G.pentagonWeight_eq_prod_coveredSquares R C, D.commute_pentagon_coveredSquares h]
  rw [hpentagon, ← G.OMonomial_swapColumns_eq_rename_of_coveredColumns R
    D.rectangle.toGridRectangle (D.rectangle_mem_coveredColumns_iff h), mul_comm]

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
