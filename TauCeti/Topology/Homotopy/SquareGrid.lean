/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Subpath

/-!
# Rectangular subdivisions of a homotopy square

A rectangular cell of a continuous square can be reparameterized as a unit square, and its two
boundary routes from the lower-left to the upper-right corner are homotopic. These facts are used
with the existing grid-subdivision theorem to turn path homotopies into local relations for an
open-cover fundamental-groupoid calculation.

The homotopy of boundary routes follows from contractibility of the square, as in Brown,
*Topology and Groupoids*, Chapters 6--7.
-/

public section

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

universe v

namespace TauCeti.HomotopySquare

variable {X : Type v} [TopologicalSpace X]

/-- The route along the bottom and right edges of the unit square. -/
def lowerRight : Path ((0 : unitInterval), (0 : unitInterval)) (1, 1) :=
  (Path.id.prod (Path.refl (0 : unitInterval))).trans
    ((Path.refl (1 : unitInterval)).prod Path.id)

/-- The route along the left and top edges of the unit square. -/
def leftUpper : Path ((0 : unitInterval), (0 : unitInterval)) (1, 1) :=
  ((Path.refl (0 : unitInterval)).prod Path.id).trans
    (Path.id.prod (Path.refl (1 : unitInterval)))

/-- The two edge routes of a continuous square represent the same morphism of the fundamental
groupoid of its codomain. -/
theorem lowerRight_homotopic_leftUpper (H : C(unitInterval × unitInterval, X)) :
    (lowerRight.map H.continuous).Homotopic (leftUpper.map H.continuous) := by
  let hI : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let hSquare : ContractibleSpace (unitInterval × unitInterval) := inferInstance
  let hSimply : SimplyConnectedSpace (unitInterval × unitInterval) := inferInstance
  exact (SimplyConnectedSpace.paths_homotopic lowerRight leftUpper).map H

/-- Reparameterize a rectangular cell of a homotopy square as a unit square. -/
def squareCell (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) : C(unitInterval × unitInterval, X) :=
  H.comp ⟨fun z ↦ ((Path.id.subpath a b) z.1, (Path.id.subpath c d) z.2), by
    exact ((Path.id.subpath a b).continuous.comp continuous_fst).prodMk
      ((Path.id.subpath c d).continuous.comp continuous_snd)⟩

@[simp]
lemma squareCell_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (z : unitInterval × unitInterval) :
    squareCell H a b c d z = H ((Path.id.subpath a b) z.1, (Path.id.subpath c d) z.2) :=
  by simp [squareCell]

/-- The bottom edge of a reparameterized cell is the horizontal subpath at height `c`. -/
@[simp]
lemma squareCell_bottom_apply (H : C(unitInterval × unitInterval, X))
    (a b c d t : unitInterval) :
    ((Path.id.prod (Path.refl (0 : unitInterval))).map
      (squareCell H a b c d).continuous) t = H ((Path.id.subpath a b) t, c) := by
  change H ((Path.id.subpath a b) t, (Path.id.subpath c d) 0) = _
  simp

/-- The right edge of a reparameterized cell is the vertical subpath at `b`. -/
@[simp]
lemma squareCell_right_apply (H : C(unitInterval × unitInterval, X))
    (a b c d t : unitInterval) :
    (((Path.refl (1 : unitInterval)).prod Path.id).map
      (squareCell H a b c d).continuous) t = H (b, (Path.id.subpath c d) t) := by
  change H ((Path.id.subpath a b) 1, (Path.id.subpath c d) t) = _
  simp

/-- The left edge of a reparameterized cell is the vertical subpath at `a`. -/
@[simp]
lemma squareCell_left_apply (H : C(unitInterval × unitInterval, X))
    (a b c d t : unitInterval) :
    (((Path.refl (0 : unitInterval)).prod Path.id).map
      (squareCell H a b c d).continuous) t = H (a, (Path.id.subpath c d) t) := by
  change H ((Path.id.subpath a b) 0, (Path.id.subpath c d) t) = _
  simp

/-- The top edge of a reparameterized cell is the horizontal subpath at height `d`. -/
@[simp]
lemma squareCell_top_apply (H : C(unitInterval × unitInterval, X))
    (a b c d t : unitInterval) :
    ((Path.id.prod (Path.refl (1 : unitInterval))).map
      (squareCell H a b c d).continuous) t = H ((Path.id.subpath a b) t, d) := by
  change H ((Path.id.subpath a b) t, (Path.id.subpath c d) 1) = _
  simp

/-- A cell whose image lies in `V`, regarded as a map with codomain `V`. -/
def squareCellIn (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    C(unitInterval × unitInterval, V) :=
  ⟨fun z ↦ ⟨squareCell H a b c d z, hV (by
    constructor
    · have hr := Set.mem_range_self z.1 (f := Path.id.subpath a b)
      rw [Path.range_subpath_of_le _ _ _ hab] at hr
      simpa using hr
    · have hr := Set.mem_range_self z.2 (f := Path.id.subpath c d)
      rw [Path.range_subpath_of_le _ _ _ hcd] at hr
      simpa using hr)⟩,
    (squareCell H a b c d).continuous.subtype_mk _⟩

@[simp]
lemma squareCellIn_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V)
    (z : unitInterval × unitInterval) :
    (squareCellIn H a b c d hab hcd V hV z).1 = squareCell H a b c d z :=
  by simp [squareCellIn]

/-- The bottom edge of a cell, valued in the cover member containing it. -/
def squareCellBottom (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    Path (squareCellIn H a b c d hab hcd V hV (0, 0))
      (squareCellIn H a b c d hab hcd V hV (1, 0)) :=
  (Path.id.prod (Path.refl (0 : unitInterval))).map
    (squareCellIn H a b c d hab hcd V hV).continuous

/-- The right edge of a cell, valued in the cover member containing it. -/
def squareCellRight (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    Path (squareCellIn H a b c d hab hcd V hV (1, 0))
      (squareCellIn H a b c d hab hcd V hV (1, 1)) :=
  ((Path.refl (1 : unitInterval)).prod Path.id).map
    (squareCellIn H a b c d hab hcd V hV).continuous

/-- The left edge of a cell, valued in the cover member containing it. -/
def squareCellLeft (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    Path (squareCellIn H a b c d hab hcd V hV (0, 0))
      (squareCellIn H a b c d hab hcd V hV (0, 1)) :=
  ((Path.refl (0 : unitInterval)).prod Path.id).map
    (squareCellIn H a b c d hab hcd V hV).continuous

/-- The top edge of a cell, valued in the cover member containing it. -/
def squareCellTop (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    Path (squareCellIn H a b c d hab hcd V hV (0, 1))
      (squareCellIn H a b c d hab hcd V hV (1, 1)) :=
  (Path.id.prod (Path.refl (1 : unitInterval))).map
    (squareCellIn H a b c d hab hcd V hV).continuous

/-- The bottom edge of a cell, viewed in the ambient space. -/
@[simp]
lemma squareCellBottom_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) (t : unitInterval) :
    (squareCellBottom H a b c d hab hcd V hV t).1 =
      H ((Path.id.subpath a b) t, c) := by
  change H ((Path.id.subpath a b) t, (Path.id.subpath c d) 0) = _
  simp

/-- The right edge of a cell, viewed in the ambient space. -/
@[simp]
lemma squareCellRight_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) (t : unitInterval) :
    (squareCellRight H a b c d hab hcd V hV t).1 =
      H (b, (Path.id.subpath c d) t) := by
  change H ((Path.id.subpath a b) 1, (Path.id.subpath c d) t) = _
  simp

/-- The left edge of a cell, viewed in the ambient space. -/
@[simp]
lemma squareCellLeft_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) (t : unitInterval) :
    (squareCellLeft H a b c d hab hcd V hV t).1 =
      H (a, (Path.id.subpath c d) t) := by
  change H ((Path.id.subpath a b) 0, (Path.id.subpath c d) t) = _
  simp

/-- The top edge of a cell, viewed in the ambient space. -/
@[simp]
lemma squareCellTop_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) (t : unitInterval) :
    (squareCellTop H a b c d hab hcd V hV t).1 =
      H ((Path.id.subpath a b) t, d) := by
  change H ((Path.id.subpath a b) t, (Path.id.subpath c d) 1) = _
  simp

/-- The bottom-right boundary route is the composite of the named cell edges. -/
theorem squareCellBottom_trans_right (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    (squareCellBottom H a b c d hab hcd V hV).trans
      (squareCellRight H a b c d hab hcd V hV) =
        lowerRight.map (squareCellIn H a b c d hab hcd V hV).continuous := by
  simp only [squareCellBottom, squareCellRight, lowerRight, Path.map_trans]

/-- The left-top boundary route is the composite of the named cell edges. -/
theorem squareCellLeft_trans_top (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Set X) (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    (squareCellLeft H a b c d hab hcd V hV).trans
      (squareCellTop H a b c d hab hcd V hV) =
        leftUpper.map (squareCellIn H a b c d hab hcd V hV).continuous := by
  simp only [squareCellLeft, squareCellTop, leftUpper, Path.map_trans]

end TauCeti.HomotopySquare
