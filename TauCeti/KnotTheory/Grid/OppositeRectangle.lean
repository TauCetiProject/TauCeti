/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Card
import TauCeti.KnotTheory.Grid.Rectangle

/-!
# Opposite grid rectangles

This file records the elementary reversal operation for oriented rectangles between grid
states. A rectangle from `x` to `y` has the two states exchange rows in two columns; reading the
same data with the side columns reversed gives an oriented rectangle from `y` back to `x`.

The operation is small, but it is useful bookkeeping for later rectangle-pairing arguments in
the fully blocked grid differential: once a rectangle is available from `x` to `y`, the
oppositely oriented rectangle is available with the expected source, target, sides, and corner
identities. This file deliberately does not claim that emptiness or marking avoidance is
preserved under this reversal: on the torus, reversing the horizontal direction changes the
column interval to its complementary interval.

## Main definitions

* `TauCeti.GridRectangleBetween.symm`: the opposite rectangle from `y` to `x`.

## References

This supplies a prerequisite for `TauCetiRoadmap/HeegaardFloer/README.md`, Lane G.3, "The
complexes and `∂² = 0`", specifically the rectangle-pairing bookkeeping used in the
juxtaposition case analysis for the fully blocked grid complex. The terminology follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- The opposite oriented rectangle, obtained by reversing the two side columns.

If `R` goes from `x` to `y`, then `R.symm` goes from `y` back to `x`. It has the same two
horizontal side rows and traverses the complementary horizontal direction on the torus. -/
def symm (R : GridRectangleBetween x y) : GridRectangleBetween y x where
  left := R.right
  right := R.left
  left_ne_right := R.left_ne_right.symm
  map_left := R.map_left.symm
  map_right := R.map_right.symm
  map_of_ne c hleft hright := (R.map_of_ne c hright hleft).symm

@[simp]
theorem symm_left (R : GridRectangleBetween x y) : R.symm.left = R.right :=
  rfl

@[simp]
theorem symm_right (R : GridRectangleBetween x y) : R.symm.right = R.left :=
  rfl

/-- Reversing a rectangle twice gives the original rectangle. -/
@[simp]
theorem symm_symm (R : GridRectangleBetween x y) : R.symm.symm = R := by
  cases R
  rfl

@[simp]
theorem symm_inj {R S : GridRectangleBetween x y} : R.symm = S.symm ↔ R = S := by
  constructor
  · intro h
    simpa using congrArg symm h
  · intro h
    simp [h]

/-- Opposite rectangles give an equivalence between rectangles from `x` to `y` and from `y`
to `x`. -/
def symmEquiv (x y : GridState n) : GridRectangleBetween x y ≃ GridRectangleBetween y x where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

@[simp]
theorem symmEquiv_apply (R : GridRectangleBetween x y) :
    symmEquiv x y R = R.symm :=
  rfl

@[simp]
theorem symmEquiv_symm_apply (R : GridRectangleBetween y x) :
    (symmEquiv x y).symm R = R.symm :=
  rfl

@[simp]
theorem symm_bottom (R : GridRectangleBetween x y) : R.symm.bottom = R.bottom := by
  simp [bottom, symm, R.map_right]

@[simp]
theorem symm_top (R : GridRectangleBetween x y) : R.symm.top = R.top := by
  simp [top, symm, R.map_left]

@[simp]
theorem symm_toGridRectangle_left (R : GridRectangleBetween x y) :
    R.symm.toGridRectangle.left = R.right :=
  rfl

@[simp]
theorem symm_toGridRectangle_right (R : GridRectangleBetween x y) :
    R.symm.toGridRectangle.right = R.left :=
  rfl

@[simp]
theorem symm_toGridRectangle_bottom (R : GridRectangleBetween x y) :
    R.symm.toGridRectangle.bottom = R.bottom := by
  simp [toGridRectangle]

@[simp]
theorem symm_toGridRectangle_top (R : GridRectangleBetween x y) :
    R.symm.toGridRectangle.top = R.top := by
  simp [toGridRectangle]

@[simp]
theorem symm_left_bottom_mem_source (R : GridRectangleBetween x y) :
    (R.symm.left, R.symm.bottom) ∈ y.pointSet := by
  simpa using R.right_bottom_mem_target

@[simp]
theorem symm_right_top_mem_source (R : GridRectangleBetween x y) :
    (R.symm.right, R.symm.top) ∈ y.pointSet := by
  simpa using R.left_top_mem_target

@[simp]
theorem symm_left_top_mem_target (R : GridRectangleBetween x y) :
    (R.symm.left, R.symm.top) ∈ x.pointSet := by
  simpa using R.right_top_mem_source

@[simp]
theorem symm_right_bottom_mem_target (R : GridRectangleBetween x y) :
    (R.symm.right, R.symm.bottom) ∈ x.pointSet := by
  simpa using R.left_bottom_mem_source

/-- Reversal preserves membership in the finite set of all oriented rectangles, now in the
reverse direction. -/
theorem symm_mem_all (R : GridRectangleBetween x y) : R.symm ∈ all y x :=
  mem_all R.symm

/-- There are as many oriented rectangles from `x` to `y` as from `y` to `x`. -/
theorem card_all_comm (x y : GridState n) : (all x y).card = (all y x).card := by
  classical
  simp [all, Fintype.card_congr (symmEquiv x y)]

end GridRectangleBetween

end TauCeti
