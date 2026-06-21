/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import TauCeti.KnotTheory.Grid.Complex

/-!
# Symmetries of the fully blocked grid differential

The grid-combinatorial lane already records that the diagonal reflection and the `O`/`X`
marking swap of a grid diagram leave the Maslov and Alexander gradings unchanged
(`Gradings.lean`, `GradingInteger.lean`). This file proves the matching statements one level
up, on the chain complex itself: both symmetries carry fully blocked empty rectangles to fully
blocked empty rectangles, so the rectangle count whose parity defines the differential is
preserved.

The key geometric step is that the diagonal reflection turns an oriented rectangle from `x` to
`y` into an oriented rectangle from `x.transpose` to `y.transpose` whose interior is the
diagonal reflection of the original interior. Because the reflection is injective on squares,
it preserves the two finite-set disjointness conditions (emptiness and marking avoidance), so
it restricts to a bijection of fully blocked rectangles. The marking swap is even simpler: the
marking-avoidance condition only refers to the union `O ∪ X`, which the swap fixes.

## Main definitions

* `TauCeti.GridRectangleBetween.transpose`: the diagonal reflection of an oriented rectangle.

## Main results

* `TauCeti.GridRectangleBetween.interior_transpose`: the reflected rectangle's interior is the
  diagonal reflection of the original interior.
* `TauCeti.GridRectangleBetween.isEmpty_transpose` and
  `TauCeti.GridRectangleBetween.avoidsMarkings_transpose`: emptiness and marking avoidance are
  preserved by the reflection.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_transpose`: the fully blocked rectangle count
  is preserved by the diagonal reflection.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_swapMarkings` and
  `TauCeti.GridDiagram.fullyBlockedDifferential_swapMarkings`: the count and the whole
  differential are preserved by the marking swap.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8
("Symmetries and the genus bound"), together with that roadmap's standing convention to "state
invariance naturality-ready": these are the chain-level symmetries of the fully blocked grid
complex on which an invariance statement is later built. The diagonal and marking symmetries
follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- The diagonal reflection of an oriented rectangle from `x` to `y`, an oriented rectangle from
`x.transpose` to `y.transpose`.

Reflecting across the main diagonal exchanges the side columns with the side rows: the new side
columns are the two rows `x R.left` and `x R.right` that `R` connects. -/
def transpose (R : GridRectangleBetween x y) :
    GridRectangleBetween x.transpose y.transpose where
  left := R.bottom
  right := R.top
  left_ne_right := R.bottom_ne_top
  map_left := by
    simp only [GridRectangleBetween.bottom, GridRectangleBetween.top]
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_eq]
    exact R.map_right.symm
  map_right := by
    simp only [GridRectangleBetween.bottom, GridRectangleBetween.top]
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_eq]
    exact R.map_left.symm
  map_of_ne c hl hr := by
    have hsymm : x (x.toPerm.symm c) = c := Equiv.apply_symm_apply _ _
    have hd_left : x.toPerm.symm c ≠ R.left := by
      intro h; rw [h] at hsymm; exact hl hsymm.symm
    have hd_right : x.toPerm.symm c ≠ R.right := by
      intro h; rw [h] at hsymm; exact hr hsymm.symm
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_eq,
      R.map_of_ne _ hd_left hd_right]
    exact hsymm.symm

/-- The reflected rectangle's initial side column is the original initial side row. -/
@[simp]
theorem transpose_left (R : GridRectangleBetween x y) : R.transpose.left = R.bottom :=
  rfl

/-- The reflected rectangle's terminal side column is the original terminal side row. -/
@[simp]
theorem transpose_right (R : GridRectangleBetween x y) : R.transpose.right = R.top :=
  rfl

/-- The reflected rectangle's initial side row is the original initial side column. -/
@[simp]
theorem transpose_bottom (R : GridRectangleBetween x y) : R.transpose.bottom = R.left := by
  simp only [GridRectangleBetween.bottom, transpose_left, GridState.transpose_apply,
    Equiv.symm_apply_apply]

/-- The reflected rectangle's terminal side row is the original terminal side column. -/
@[simp]
theorem transpose_top (R : GridRectangleBetween x y) : R.transpose.top = R.right := by
  simp only [GridRectangleBetween.top, transpose_right, GridState.transpose_apply,
    Equiv.symm_apply_apply]

/-- The toroidal rectangle of the reflected oriented rectangle, written out by its four sides. -/
@[simp]
theorem transpose_toGridRectangle (R : GridRectangleBetween x y) :
    R.transpose.toGridRectangle =
      { left := R.bottom, right := R.top, bottom := R.left, top := R.right } := by
  unfold GridRectangleBetween.toGridRectangle
  rw [transpose_bottom, transpose_top, transpose_left, transpose_right]

/-- Two oriented rectangles between the same states with equal side columns are equal. -/
theorem eq_of_sides {R S : GridRectangleBetween x y} (hleft : R.left = S.left)
    (hright : R.right = S.right) : R = S := by
  obtain ⟨_, _, _, _, _, _⟩ := R
  obtain ⟨_, _, _, _, _, _⟩ := S
  obtain rfl : _ = _ := hleft
  obtain rfl : _ = _ := hright
  rfl

/-- Reflecting an oriented rectangle twice gives the original rectangle. -/
@[simp]
theorem transpose_transpose (R : GridRectangleBetween x y) : R.transpose.transpose = R :=
  eq_of_sides (transpose_bottom R) (transpose_top R)

/-- The diagonal reflection is injective on oriented rectangles. -/
theorem transpose_injective :
    Function.Injective
      (transpose : GridRectangleBetween x y → GridRectangleBetween x.transpose y.transpose) := by
  intro R S h
  have hl := congrArg (·.left) h
  have hr := congrArg (·.right) h
  simp only [transpose_left, transpose_right, GridRectangleBetween.bottom,
    GridRectangleBetween.top] at hl hr
  exact eq_of_sides (x.toPerm.injective hl) (x.toPerm.injective hr)

/-- The interior of the reflected rectangle is the diagonal reflection of the interior of the
original rectangle. -/
theorem interior_transpose (R : GridRectangleBetween x y) :
    R.transpose.toGridRectangle.interior = R.toGridRectangle.interior.image Prod.swap := by
  rw [transpose_toGridRectangle]
  ext ⟨a, b⟩
  constructor
  · intro hab
    rw [GridRectangle.mem_interior] at hab
    simp only [GridRectangle.mem_columnInterior, GridRectangle.mem_rowInterior] at hab
    rw [Finset.mem_image]
    refine ⟨(b, a), ?_, rfl⟩
    rw [GridRectangle.mem_interior]
    simp only [GridRectangle.mem_columnInterior, GridRectangle.mem_rowInterior]
    exact ⟨hab.2, hab.1⟩
  · intro hab
    rw [Finset.mem_image] at hab
    obtain ⟨⟨c, d⟩, hcd, hswap⟩ := hab
    rw [GridRectangle.mem_interior] at hcd
    simp only [GridRectangle.mem_columnInterior, GridRectangle.mem_rowInterior] at hcd
    rw [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
    obtain ⟨rfl, rfl⟩ := hswap
    rw [GridRectangle.mem_interior]
    simp only [GridRectangle.mem_columnInterior, GridRectangle.mem_rowInterior]
    exact ⟨hcd.2, hcd.1⟩

/-- The diagonal reflection preserves emptiness of a rectangle between grid states. -/
theorem isEmpty_transpose (R : GridRectangleBetween x y) :
    R.transpose.IsEmpty ↔ R.IsEmpty := by
  unfold GridRectangleBetween.IsEmpty GridRectangle.IsEmptyFor
  rw [interior_transpose, GridState.transpose_pointSet,
    Finset.disjoint_image Prod.swap_injective]

/-- The diagonal reflection preserves marking avoidance of a rectangle between grid states. -/
theorem avoidsMarkings_transpose (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.transpose.AvoidsMarkings G.transpose ↔ R.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings GridRectangle.AvoidsMarkings
  rw [interior_transpose, G.transpose_OSet, G.transpose_XSet, ← Finset.image_union,
    Finset.disjoint_image Prod.swap_injective]

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The diagonal reflection of a fully blocked rectangle is a fully blocked rectangle for the
reflected diagram. -/
theorem mem_fullyBlockedRectangles_transpose (x y : GridState n) (R : GridRectangleBetween x y) :
    R.transpose ∈ G.transpose.fullyBlockedRectangles x.transpose y.transpose ↔
      R ∈ G.fullyBlockedRectangles x y := by
  simp only [mem_fullyBlockedRectangles, GridRectangleBetween.isEmpty_transpose,
    GridRectangleBetween.avoidsMarkings_transpose]

/-- The fully blocked rectangle count is invariant under the diagonal reflection of a grid
diagram and its two states. This is the matrix-coefficient form of the statement that the
diagonal reflection is a chain symmetry of the fully blocked grid complex. -/
theorem fullyBlockedRectangleCount_transpose (x y : GridState n) :
    G.transpose.fullyBlockedRectangleCount x.transpose y.transpose =
      G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_def, fullyBlockedRectangleCount_def]
  congr 1
  refine Finset.card_bij' (fun S _ => S.transpose) (fun R _ => R.transpose) ?_ ?_ ?_ ?_
  · intro S hS
    exact (G.transpose.mem_fullyBlockedRectangles_transpose x.transpose y.transpose S).mpr hS
  · intro R hR
    exact (G.mem_fullyBlockedRectangles_transpose x y R).mpr hR
  · intro S _
    exact GridRectangleBetween.transpose_transpose S
  · intro R _
    exact GridRectangleBetween.transpose_transpose R

/-- The fully blocked rectangles are unchanged by swapping the `O` and `X` markings, since
marking avoidance only refers to the union of the two marking sets. -/
@[simp]
theorem fullyBlockedRectangles_swapMarkings (x y : GridState n) :
    G.swapMarkings.fullyBlockedRectangles x y = G.fullyBlockedRectangles x y := by
  ext R
  rw [mem_fullyBlockedRectangles, mem_fullyBlockedRectangles]
  refine and_congr_right fun _ => ?_
  rw [GridRectangleBetween.avoidsMarkings_iff, GridRectangleBetween.avoidsMarkings_iff,
    swapMarkings_OSet, swapMarkings_XSet]
  exact and_comm

/-- The fully blocked rectangle count is invariant under swapping the `O` and `X` markings. -/
@[simp]
theorem fullyBlockedRectangleCount_swapMarkings (x y : GridState n) :
    G.swapMarkings.fullyBlockedRectangleCount x y = G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_def, fullyBlockedRectangleCount_def,
    fullyBlockedRectangles_swapMarkings]

/-- The generator row of the fully blocked differential is invariant under swapping the `O` and
`X` markings. -/
@[simp]
theorem fullyBlockedDifferentialOnGenerator_swapMarkings (x : GridState n) :
    G.swapMarkings.fullyBlockedDifferentialOnGenerator x =
      G.fullyBlockedDifferentialOnGenerator x := by
  unfold fullyBlockedDifferentialOnGenerator
  simp_rw [fullyBlockedRectangleCount_swapMarkings]

/-- The whole fully blocked grid differential is invariant under swapping the `O` and `X`
markings. -/
@[simp]
theorem fullyBlockedDifferential_swapMarkings :
    G.swapMarkings.fullyBlockedDifferential = G.fullyBlockedDifferential := by
  have h : (fun x : GridState n =>
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight
          (G.swapMarkings.fullyBlockedDifferentialOnGenerator x)) =
      fun x : GridState n =>
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight
          (G.fullyBlockedDifferentialOnGenerator x) := by
    funext x
    rw [fullyBlockedDifferentialOnGenerator_swapMarkings]
  unfold fullyBlockedDifferential
  rw [h]

end GridDiagram

end TauCeti
