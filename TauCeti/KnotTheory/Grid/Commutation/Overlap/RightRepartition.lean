/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Right

/-!
# Repartition of terminal-side overlap recuts

In the pentagon chain-map equation, a rectangle followed by a pentagon can have their terminal
vertical side in common. Exactly one rectangle of the recut inherits that side and becomes a
pentagon. This file identifies both promoted decompositions with the ordinary rectangle recut and
transfers emptiness and the covered-square repartition to them. These are the geometric facts used
when comparing the two weighted decompositions in the commutation argument.

The juxtaposition argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Section 5.1. The monomial identity below concerns the underlying rectangles; pentagon
weights also account for the two columns next to the commuted grid line.
-/

public section

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Forgetting the turn row after the first terminal-side promotion gives the ordinary recut. -/
@[simp]
theorem recutRightEqRightFirst_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).toRectangleDecomposition =
      D.recutOfIsEmpty hone hrectangle hpentagon := by
  apply GridRectangleDecomposition.ext
  · simp
  · simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
      recutRightEqRightFirst_pentagon_right] using
      (hfirst.trans D.pentagon.right_eq).symm
  · simp
  · simp

/-- The promoted first-branch decomposition is a genuine recut of the original two rectangles. -/
theorem isRecut_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    D.toRectangleDecomposition.IsRecut
      (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).toRectangleDecomposition := by
  rw [D.recutRightEqRightFirst_toRectangleDecomposition hcommon hone
        hrectangle hpentagon hfirst,
    D.recutOfIsEmpty_eq_recut hone hrectangle hpentagon]
  exact D.toRectangleDecomposition.isRecut_recut hone _ _

/-- The pentagon promoted from the first recut rectangle remains empty. -/
@[simp]
theorem isEmpty_pentagon_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).pentagon.IsEmpty := by
  have h := (D.isRecut_recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).isEmpty_first
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h

/-- The rectangle left after promoting the first recut rectangle remains empty. -/
@[simp]
theorem isEmpty_rectangle_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).rectangle.IsEmpty := by
  have h := (D.isRecut_recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).isEmpty_second
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h

/-- The two underlying rectangles of the first promotion cover precisely the original region. -/
theorem coveredSquares_union_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).pentagon.toGridRectangle.coveredSquares ∪
      (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).rectangle.toGridRectangle.coveredSquares =
        D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  have h := (D.isRecut_recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).isRepartition.coveredSquares_union_eq
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using h

/-- Repartition preserves the product of the `O`-monomials of the underlying rectangles. -/
theorem OMonomial_mul_OMonomial_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
      D.pentagon.right)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R
        (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).pentagon.toGridRectangle *
      G.OMonomial R
        (D.recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).rectangle.toGridRectangle =
        G.OMonomial R D.rectangle.toGridRectangle *
          G.OMonomial R D.pentagon.toGridRectangle := by
  have h := (D.isRecut_recutRightEqRightFirst hcommon hone
        hrectangle hpentagon hfirst).isRepartition.OMonomial_mul_OMonomial G R
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using h

/-- Forgetting the turn row after the second terminal-side promotion gives the ordinary recut. -/
@[simp]
theorem recutRightEqRightSecond_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).toRectangleDecomposition =
      D.recutOfIsEmpty hone hrectangle hpentagon := by
  apply GridRectangleDecomposition.ext
  · simp
  · simp
  · simp
  · simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
      recutRightEqRightSecond_pentagon_right] using
      (hsecond.trans D.pentagon.right_eq).symm

/-- The promoted second-branch decomposition is a genuine recut of the original rectangles. -/
theorem isRecut_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    D.toRectangleDecomposition.IsRecut
      (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).toRectangleDecomposition := by
  rw [D.recutRightEqRightSecond_toRectangleDecomposition hcommon hone
        hrectangle hpentagon hsecond,
    D.recutOfIsEmpty_eq_recut hone hrectangle hpentagon]
  exact D.toRectangleDecomposition.isRecut_recut hone _ _

/-- The first rectangle in the second-branch promotion remains empty. -/
@[simp]
theorem isEmpty_rectangle_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).rectangle.IsEmpty := by
  have h := (D.isRecut_recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).isEmpty_first
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_middle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h

/-- The pentagon promoted from the second recut rectangle remains empty. -/
@[simp]
theorem isEmpty_pentagon_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).pentagon.IsEmpty := by
  have h := (D.isRecut_recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).isEmpty_second
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_middle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h

/-- The two underlying rectangles of the second promotion cover precisely the original region. -/
theorem coveredSquares_union_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).rectangle.toGridRectangle.coveredSquares ∪
      (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).pentagon.toGridRectangle.coveredSquares =
        D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  have h := (D.isRecut_recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).isRepartition.coveredSquares_union_eq
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using h

/-- Repartition preserves the product of the `O`-monomials of the underlying rectangles. -/
theorem OMonomial_mul_OMonomial_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R
        (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).rectangle.toGridRectangle *
      G.OMonomial R
        (D.recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).pentagon.toGridRectangle =
        G.OMonomial R D.rectangle.toGridRectangle *
          G.OMonomial R D.pentagon.toGridRectangle := by
  have h := (D.isRecut_recutRightEqRightSecond hcommon hone
        hrectangle hpentagon hsecond).isRepartition.OMonomial_mul_OMonomial G R
  simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using h

end TauCeti.GridRectanglePentagonDecomposition
