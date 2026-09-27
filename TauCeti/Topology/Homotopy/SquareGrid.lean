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

end TauCeti.HomotopySquare
